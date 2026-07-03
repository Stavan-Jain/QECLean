# A13 L2 — formalizing the rank corollary `dim (1+σ)H₁ = k̃ − k`

**Status: in progress (2026-07-03). L2a core landed; see Execution status
below.** Branch `claude/a13-bockstein-equality` (off PR #53, rebased —
`BBDeckTower.lean` from the merged OQ1 PR #54 is now on-branch). Prereq
reading: [`A13_result.md`](A13_result.md) (§1 defect identity, §5 the L2
scope note), `BocksteinLift.lean` (L1, done).

## Execution status (2026-07-03)

The rebase onto PR #53 pulled in `BBDeckTower.lean` (OQ1 tower work),
which **defines `EpsFree ε N`** (`ε^t x = 0 → ∃ y, x = ε^{N-t} y`) — the
same ring hypothesis L2a needs. This unified the two deck lines: L2a's
`Ann(ε̂) = (ε̂³)` is `EpsFree ε̂ 4` at `t = 1`, the hypothesis BOTH
`BBDeckTower.eps_mem_of_deckTrivial` (OQ1) and
`BocksteinLift.bockstein_element_form` (OQ2) consume unproven.

**Landed, axiom-clean (`QEC/…/Homological/BBEpsFree.lean`, commit `b7ee838`):**
- `epsFree_quotXpow` — `EpsFree (mk X) N` in `R[X]/(X^N)` for any
  `CommRing R` (chain-ring / local block; `X^t` monic ⟹ regular ⟹
  cancels). Generalizes `BocksteinLift.deckRing_ann` (its `R=𝔽₂,N=4,t=1`
  slice). This is the base ring `Λ`.
- `epsFree_of_free` — `EpsFree` transfers from `Λ` to any free
  `Λ`-algebra `S` (basis expansion + coordinatewise division). The
  "annihilator across a free module" step.
- `hann_of_epsFree` — `EpsFree ε 4 ⟹` `BocksteinLift`'s `hann`, making
  the unification explicit.

**Effect on the plan:** general L2a (`EpsFree` for `𝔽₂[G]`) is now reduced
to a **single remaining lemma** — `Module.Free 𝔽₂[⟨σ⟩] 𝔽₂[G]` (coset
basis) plus the ring iso `𝔽₂[⟨σ⟩] ≅ 𝔽₂[Y]/(Y^N)` — after which
`epsFree_of_free ∘ epsFree_quotXpow` closes it. Confirmed no mathlib
support for subgroup-algebra freeness (`MonoidAlgebra.instFree` is base-
ring only), so this remains the from-scratch wildcard (Phase 3 below).
Phases 0/1/2 (concrete equality, `E ≥ k̃−k` inequality, bridge) are
untouched and remain the recommended next entry points.

## 0. What L2 is, and what L1 already gave

L1 (done, axiom-clean, `QEC/Stabilizer/Framework/Homological/`
`BocksteinLift.lean`) proved the **sharpest element-level form** of the
Bockstein equality: over any `CommRing` with `char 2` and
`Ann(ε) = (ε³)`, in the cover ring `R ⧸ (ε²)`, whenever `Az, Bz ∈ εR̃`
then `A·ε⁻¹(Bz) + B·ε⁻¹(Az) ∈ ε(A,B)` (`bockstein_element_form`), plus an
**unconditional** instance on the ℤ/4 chain block `F₂[X]/(X⁴)`
(`bockstein_element_form_deck`).

L2 upgrades that element-level fact into the **dimension theorem** the
paper wants, in the repo's actual chain complexes:

- **L2b (the rank corollary).**
  `dim_F₂ (1+σ)·H₁(cover) = dim H₁(cover) − dim H₁(base)` (`= k̃ − k`),
  hence the deck-module structure `H₁ ≅ D^{k̃−k} ⊕ F₂^{2k−k̃}`.
- **L2a (the general ring input).** `Ann_{F₂[Ĝ]}(ε̂) = (ε̂³)` for the
  Frattini-lift algebra of *every* cover (not just the single ℤ/4 block
  L1 discharged), so the element form holds for real cover rings.

L2b is the headline; L2a is the hypothesis L2b's equality step consumes.

## 1. Target Lean statements (what "done" looks like)

Over `D : XDoubleCoverData G H` (`BBCover.lean:59`), with `σ = deckShift1`
(`BBCover.lean:148`), `ε = 1 + σ`, and `H1`, `cycles`, `boundaries`,
`finrank` from `Code.lean`:

```lean
-- L2b headline (repo language)
theorem deck_finrank_eq (D : XDoubleCoverData G H) :
    Module.finrank (ZMod 2) (epsH1Range D)                    -- E := dim (1+σ)H₁
      = Module.finrank (ZMod 2) D.coverComplex.H1             -- k̃
        - Module.finrank (ZMod 2) D.baseComplex.H1            -- k

-- L2b structure corollary
theorem coverH1_deckModule_iso (D : XDoubleCoverData G H) :
    Nonempty (D.coverComplex.H1 ≃ₗ[ZMod 2] {- D^{k̃−k} ⊕ F₂^{2k−k̃} -})
```

`epsH1Range D` = range of the endomorphism `H1 → H1` induced by `deckShift1`
+ id (it descends because `deckShift1` commutes with both boundary maps —
that commutation is implicit in `pull1_push1` and must be extracted).

The **unconditional inequality** `E ≥ k̃ − k` (A12 part 2) is a natural
sub-theorem, provable *without* L2a, and worth landing on its own:

```lean
theorem deck_finrank_ge (D : XDoubleCoverData G H) :
    Module.finrank (ZMod 2) (epsH1Range D)
      ≥ Module.finrank (ZMod 2) D.coverComplex.H1
        - Module.finrank (ZMod 2) D.baseComplex.H1
```

## 2. Ground truth from reconnaissance

### 2.1 Repo (all hand-rolled linear algebra over `ZMod 2`)

| Piece | Where | Notes |
|---|---|---|
| chain groups `C₀=G`, `C₁=G×Fin 2`, `C₂=G`; `conv` product | `BBChainComplex.lean:48,400` | `conv a b = ∑ₕ a h * b(g−h)` — the group algebra `F₂[G]` product on **function space**, no `MonoidAlgebra`/`Polynomial` type |
| `∂₁,∂₂` as `LinearMap` (mult by (A,B),(B,A)) | `BBChainComplex.lean:207–280` | |
| `H1 := cycles ⧸ boundaries`; `cycles=ker ∂₁`, `boundaries=range ∂₂` | `Code.lean:84–114` | **`k = finrank H1` exists** |
| `finrank_H1_eq_cycles_sub_boundaries`, `rank_nullity_boundary1/2` | `Code.lean:131–171` | dimension bookkeeping already in repo idiom |
| `coverComplex`, `baseComplex` | `BBCover.lean:125,128` | both are `bbChainComplex`; `k̃`, `k` are their `finrank H1` |
| deck `σ = deckShift1`, push/pull transfer as `LinearMap` | `BBCover.lean:134–222` | |
| **transfer SES at chain level**: `pull1_push1 : τ∘p·v = v+σv = (1+σ)v`; `push1_pull1_eq_zero`; `pull1_injective`; `push1_surjective`; `push1_eq_zero_iff : ker p = range τ` | `BBCover.lean:276–303` | the SES `0→εK̃→K̃→K̄→0` is essentially present on 1-chains |
| **chain-level connecting map** `seamC` (+ `seamC_mem_cycles`) | `BBCover.lean:558–657` | a δ₂-analogue already built |
| `DeckTrivialOnH1` (= `εH₁ = 0`, the `k̃=k` corner); `deckTrivial_of_bezout`/`_of_homotopy_certificate` | `BBDoubling.lean:141,198,379` | currently consumed only by the **distance** floor (`:803`), never a k-equality |

No `MonoidAlgebra`, no mathlib `HomologicalComplex`/`ShortComplex`, no CRT
block decomposition, no `k̃−k = 2g` lemma. `BBDeckTower.lean` (ℤ/2^r tower
+ descent, from the OQ1 line) is **on another branch, not in this
worktree** — potentially portable for L2a, not assumable.

### 2.2 mathlib (v4.30.0-rc2)

- **finrank toolkit is complete** for the direct route: `LinearMap.finrank_range_add_finrank_ker`, `Submodule.finrank_quotient_add_finrank`, `Submodule.finrank_sup_add_finrank_inf_eq` (incl-excl), `Submodule.finrank_map_le`, `Submodule.liftQ`/`ker_liftQ`, `Submodule.comap_map_eq`, `Module.finrank_directSum`.
- **module-level snake lemma exists**: `SnakeLemma.δ` / `δ'` (concrete `LinearMap`s, no category theory) — a middle path to the connecting map + exactness without packaging as `HomologicalComplex`. The categorical LES (`CategoryTheory.ShortComplex.ShortExact.δ`, `homology_exact₂/₃`, `composableArrows₅_exact`) exists too but needs `ModuleCat`/`ShortExact` boilerplate and *still* bottoms out in rank-nullity — **not worth it here**.
- **freeness of a group algebra over a subgroup algebra is NOT in mathlib.** `MonoidAlgebra.instFree` only covers freeness over the *base* ring. No annihilator-transfer lemma (`Ann_M(a) = (Ann_R a)·M`) either. These are the L2a gaps that must be hand-built.
- **truncated-polynomial support**: `IsAdjoinRootMonic.basis` (basis `{1,…,Xⁿ⁻¹}`), `Polynomial.Monic.isRegular` / `.mem_nonZeroDivisors` — lets `deckRing_ann` be re-derived over any base ring (currently it uses `NoZeroDivisors (ZMod 2)` via `decide`); relevant to L2a's local block.

### 2.3 Decisions forced by the recon

1. **L2b via direct `finrank`**, in the repo's `Code.lean` idiom, using the existing chain-level transfer exactness — not mathlib's categorical LES. (Consider `SnakeLemma.δ` only if a clean connecting map is wanted.)
2. **A bridge is required** between `BocksteinLift` (`CommRing`/`Ideal`) and the repo's `(G→ZMod 2, conv)` (whose `Pi` type already carries a *pointwise* ring instance). Route the bridge through `MonoidAlgebra (ZMod 2) (Multiplicative G)` + the ring iso `Finsupp.equivFunOnFinite`, transporting `∂ᵢ = mul by (A,B)/(B,A)` and `ε = mul by deckPoly` (`deckPoly = 1+x^{deckS}`, `BBDoubling.lean:258`).
3. **L2a is the wildcard**: no mathlib freeness/annihilator-transfer, and the tower infra is off-branch. Its general form is bespoke ring theory.

## 3. Milestones

Effort tags: S ≈ ½ day, M ≈ 1–2 days, L ≈ 3–5 days.

### Phase 0 — concrete per-code equality (S–M, no abstractions) ⭐ do first
`E = k̃ − k` for **gross and pair72** as a finite `F₂`-rank identity via
the repo's computable-rank + `native_decide` pattern (the decoder-cert
idiom): express `E`, `k̃`, `k` as ranks of explicit `ZMod 2` matrices
(∂₁, ∂₂, and `(1+σ)` restricted to a cycle basis) and `native_decide` the
equality. Delivers the structure theorem for the flagship codes
immediately, independent of L2a/L2b, and *cross-validates* the abstract
claim. Risk: representing `E` as a matrix rank (needs a computable handle
on `ker∂₁`); low. **This is the cheapest real artifact.**

### Phase 1 — the unconditional inequality `E ≥ k̃ − k` (M–L)
The direct-`finrank` diagram chase on the existing chain-level transfer
SES (`BBCover.lean:276–303`), mirroring `Code.lean`'s rank-nullity style.
Deliverables:
- `epsH1` : the endomorphism `H1 → H1` from `deckShift1` (prove it
  descends: `deckShift1` maps `cycles→cycles`, `boundaries→boundaries` —
  extract the `∂∘σ = σ∘∂` commutation).
- `deck_finrank_ge` via incl-excl (`finrank_sup_add_finrank_inf_eq`) +
  rank-nullity on the transfer maps. This *is* A12 part 2, re-proved
  homologically in Lean — valuable on its own, and no L2a needed.
Risk: the chase is intricate (tracking `ε(ker∂₁)`, `im∂₂`, base homology);
all lemmas exist. Medium–high.

### Phase 2 — the bridge + wiring the element form (M)
- `BBConvRing.lean` (new): `R_G := MonoidAlgebra (ZMod 2) (Multiplicative G)`,
  the ring iso to `(G→ZMod 2, conv)`, and lemmas `∂ᵢ = mul …`,
  `(1+σ) = mul deckPoly`. Reformulate `cycles/boundaries/H1` as `R_G`-module
  objects so `BocksteinLift` applies.
- Connect `bockstein_element_form` to the chain-level connecting composite
  (via `seamC`, `BBCover.lean:558`): show the composite `δ₁∘δ₂` on base
  homology is the map the element form kills. Output: `δ₁δ₂ = 0` at the
  concrete level (conditional on L2a's `Ann` for this cover).
Risk: the `MonoidAlgebra ≃ conv` transport is standard but verbose; the
`seamC`↔`δ` identification needs care. Medium.

### Phase 3 — L2a: `EpsFree` (⟹ `Ann(ε̂) = (ε̂³)`), general (L, wildcard)
Closes Phase 1's inequality to the equality. **Core DONE** (see Execution
status): `epsFree_quotXpow` (base ring `Λ`) + `epsFree_of_free` (transfer)
+ `hann_of_epsFree` (bridge to OQ2), all axiom-clean in `BBEpsFree.lean`.
`BBDeckTower.lean` did **not** need porting — it was merged in via the
rebase, and it *defines* `EpsFree`, so `BBEpsFree` builds directly on it.

**Remaining (the single wildcard):** the freeness instance
`Module.Free (𝔽₂[⟨σ⟩]) (𝔽₂[G])` (coset basis) plus the ring iso
`𝔽₂[⟨σ⟩] ≅ 𝔽₂[Y]/(Y^N)` (`N = 2^r`). Confirmed no mathlib support
(`MonoidAlgebra.instFree` is base-ring only; no subgroup-algebra
freeness). Build via `Basis.mk` on an ⟨σ⟩-transversal of `G`, or an
internal `Finsupp` coset direct-sum; then `epsFree_of_free` applied to
that instance + `epsFree_quotXpow` (through the iso) gives `EpsFree` for
`𝔽₂[G]`, discharging the hypothesis of BOTH deck lines. **Fallback** for
partial coverage: `m` odd (all blocks chain) via `epsFree_quotXpow`
directly + a CRT split — but CRT for `𝔽₂[G]` is also not in mathlib, so
prefer completing the coset-basis freeness.

### Phase 4 — equality + structure theorem + write-up (S–M)
`deck_finrank_eq` (Phase 1 `≥` + Phase 2/3 `δ₁δ₂=0` ⟹ `=`), then
`coverH1_deckModule_iso` (`H₁ ≅ D^{k̃−k}⊕F₂^{2k−k̃}` from `E` and `k̃`,
using `Module.finrank_directSum` and the `D = F₂[ε]/ε²`-module
classification). Update `A13_result.md`, research log, memory; `lake build`
+ `#print axioms` (target: standard three only).

## 4. Dependency graph & recommended sequencing

```
Phase 0 (per-code native_decide)   ── independent, do first (fast win + validation)
Phase 1 (E ≥ k̃−k, unconditional)  ── independent of L2a; publishable alone
        │
        ├── Phase 2 (bridge + δ₁δ₂=0 wiring) ──┐
        │                                       │
Phase 3 (L2a: Ann general) ─────────────────────┤
                                                 ▼
                                    Phase 4 (equality + structure thm)
```

Recommended order: **0 → 1 → 2 → 3 → 4**. Front-loads the sure wins
(Phase 0 gives flagship results in a day; Phase 1 re-proves A12's
inequality homologically, no wildcard). Phase 3 (the risky ring theory) is
deferred until the scaffold it plugs into (Phases 1–2) is solid, so its
risk can't strand the rest.

## 5. Risks & fallbacks

- **L2a freeness (Phase 3b/c)** — no mathlib support, off-branch tower.
  *Mitigations, in order:* port `BBDeckTower.lean`; else coset-basis
  `Basis.mk`; else per-code `Ann` by `decide` (finite, like L1's
  `deckRing_ann`) which — combined with Phase 0 — already yields the full
  structure theorem for gross/pair72 without the general lemma.
- **Bridge verbosity (Phase 2)** — the `MonoidAlgebra ≃ conv` transport
  can balloon. *Mitigation:* keep `BocksteinLift` abstract; only transport
  the three facts Phase 2 needs, don't re-express the whole complex.
- **Diagram-chase intricacy (Phase 1)** — *Mitigation:* consider
  `SnakeLemma.δ` for a ready-made connecting map + exactness at module
  level; fall back to fully manual only if its hypotheses are awkward.
- **Scope creep to full generality** — the abstract theorem over *all*
  finite-abelian `G` needs a general Frattini lift (structure theorem).
  *Mitigation:* target the concrete BB family (`ZMod (2ℓ)×ZMod m`) that
  the repo actually uses; state generality as future work.

## 6. Deliverables & definition of done

- New Lean: `BBConvRing.lean` (bridge), `BBBocksteinRank.lean`
  (`epsH1`, `deck_finrank_ge`, `deck_finrank_eq`,
  `coverH1_deckModule_iso`); L2a either ports `BBDeckTower.lean` or adds
  `BBFrattiniLift.lean`. All wired into the `Homological` umbrella
  (**grep-verify the import — the L1 umbrella edit silently failed once**).
- Per-code: `native_decide` equality for gross + pair72 (Phase 0).
- `lake build` green; `#print axioms` = `propext`/`Classical.choice`/
  `Quot.sound` (Phase-0 per-code results may additionally carry
  `ofReduceBool` from `native_decide`, acceptable and flagged).
- Notes/research-log/memory updated; the two mathlib gaps (subgroup-
  algebra freeness; annihilator transfer) recorded as candidate upstream
  contributions.

## 7. Effort summary

| Phase | Effort | Wildcard? | Status |
|---|---|---|---|
| 0 — per-code `native_decide` equality | S–M | no | not started |
| 1 — unconditional inequality `E ≥ k̃−k` | M–L | no | not started |
| 2 — bridge + element-form wiring | M | no | not started |
| 3 — L2a general `EpsFree`/`Ann(ε̂)=(ε̂³)` | L | **yes** (no mathlib support) | **core done** (`BBEpsFree`); only coset-basis freeness left |
| 4 — equality + structure thm + write-up | S–M | no | not started |

Full abstract theorem: ≈ 1.5–2.5 weeks, dominated by Phase 3. Pragmatic
milestone (flagship codes + homological inequality, Phases 0–1): ≈ 3–4
days and already a strong, citable result. Not engine-load-bearing (the
doubling program runs at `k̃ = k`); this is the mathematical-core / paper
deliverable, with L1's element form as its foundation.
