# A13 L2 — formalizing the rank corollary `dim (1+σ)H₁ = k̃ − k`

**Status: plan (2026-07-03), grounded in two reconnaissance sweeps of the
repo homological framework and of mathlib's homology / finrank / group-
algebra API. Not started.** Branch `claude/a13-bockstein-equality`
(off PR #53). Prereq reading: [`A13_result.md`](A13_result.md) (§1 defect
identity, §5 the L2 scope note), `BocksteinLift.lean` (L1, done).

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

### Phase 3 — L2a: `Ann_{F₂[Ĝ]}(ε̂) = (ε̂³)`, general (L, wildcard)
Closes Phase 1's inequality to the equality. Steps:
- **First: attempt to port `BBDeckTower.lean`** from the OQ1 branch
  (`claude/a13-deck-trivial-tower`) — it has ℤ/2^r lift + descent
  (`ε^t z = 0 ⟹ ε-free divides`), which may already contain the ℤ/4
  annihilator content. If portable, Phase 3 collapses to wiring.
- **Else build it:** (a) the Frattini lift `Ĝ` (double the `deckS` axis)
  for the concrete family `ZMod (2ℓ)×ZMod m ↦ ZMod (4ℓ)×ZMod m`, with
  `σ̂` order 4 and `R̂/(ε̂²) ≅ R̃`; (b) `F₂[Ĝ]` free over `Λ = F₂[⟨σ̂⟩] ≅
  F₂[Z₄]` via an explicit **coset basis** (no mathlib support — use
  `Basis.mk` on a transversal, or an internal `Finsupp` coset direct-sum);
  (c) annihilator transfer `Ann_{R̂}(ε̂) = (Ann_Λ ε̂)·R̂` (hand-built);
  (d) combine with the existing `deckRing_ann` (`Λ ≅ F₂[X]/(X⁴)`) to get
  `Ann(ε̂)=(ε̂³)`; (e) instantiate `bockstein_element_form`.
Risk: (b)+(c) are the bespoke ring theory with zero mathlib support — the
main cost/uncertainty of all L2. **Fallback**: prove L2a only for
`m` odd (all blocks chain) using `bockstein_element_form_deck` + a CRT
block split — but CRT for `F₂[G]` is *also* not in mathlib, so this trades
one gap for another; prefer the coset-basis route.

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

| Phase | Effort | Wildcard? |
|---|---|---|
| 0 — per-code `native_decide` equality | S–M | no |
| 1 — unconditional inequality `E ≥ k̃−k` | M–L | no |
| 2 — bridge + element-form wiring | M | no |
| 3 — L2a general `Ann(ε̂)=(ε̂³)` | L | **yes** (no mathlib support) |
| 4 — equality + structure thm + write-up | S–M | no |

Full abstract theorem: ≈ 1.5–2.5 weeks, dominated by Phase 3. Pragmatic
milestone (flagship codes + homological inequality, Phases 0–1): ≈ 3–4
days and already a strong, citable result. Not engine-load-bearing (the
doubling program runs at `k̃ = k`); this is the mathematical-core / paper
deliverable, with L1's element form as its foundation.
