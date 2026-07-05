# A13 L2 — formalizing the rank corollary `dim (1+σ)H₁ = k̃ − k`

**Status: in progress (2026-07-04). ALL LINEAR-ALGEBRA WIRING DONE. The
inequality `E ≥ k̃ − k` is a Lean theorem for every `XDoubleCoverData`;
the *equality* `E = k̃ − k` (plus `dim ker ε_* = k` and `ε_*² = 0`, i.e.
the full deck-module rank picture) is a Lean theorem conditional on the
single clean criterion `BocksteinVanishes D` (`ker τ_* ≤ range p_*` on
`H₁`, = `δ₁∘δ₂ = 0`). `EpsFree (1 + x^σ) (2^r)` is a Lean theorem for
every 2-power-order deck (any abelian `G`, any char-2 base), and composing
it with L1 gives the element form `δ₁δ₂ = 0` in every order-4 deck group
algebra (`bockstein_element_form_group_algebra`). The SOLE remaining gap
is the homological transport identifying that element fact with
`BocksteinVanishes` (the seam↔connecting-map bridge) — which is the
paper's main theorem, not wiring. See Execution status below.**
Branch `claude/a13-bockstein-equality` (off PR #53, rebased —
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

**Phase 1 core landed (commit `67b947e`, `BBBocksteinRank.lean`,
axiom-clean):** the transfer inequality's linear-algebra heart —
- `finrank_ker_comp_le : dim ker(g∘f) ≤ dim ker f + dim ker g` (restrict
  `f` to `ker(g∘f)`: range lands in `ker g`, kernel injects into `ker f`);
- `finrank_sub_le_finrank_range_comp` : given exactness `ker p = range τ`
  and `ε = τ∘p`, `dim Hc − dim Hb ≤ dim (range ε)`.
Instantiated with `Hc = H₁(cover)`, `Hb = H₁(base)`, `p = p_*`,
`τ = τ_*`, `ε_* = (1+σ)_*`, this is `E ≥ k̃−k`.

**Phase-1 instantiation LANDED (2026-07-04, `BBTransferH1.lean` +
additions to `BBCover.lean`, axiom-clean):**
- `BBCover.lean` gained `push0_surjective` (one-liner, mirror of
  `push1_surjective`) and `exists_pull_eq_add_boundary` — the full
  diagram chase **at chain level** (`p₁ v ∈ B ⟹ ∃ u ∈ Z₁(base), ∃ f,
  τ₁ u = v + ∂₂ᶜ f`), exactly the chase sketched below.
- `BBTransferH1.lean` (new, in the umbrella): `push1Cycles`/`pull1Cycles`
  (`LinearMap.restrict`), `pushH1`/`pullH1` (`Submodule.mapQ`),
  `ker_pushH1_eq_range_pullH1` (exactness at the cover), `epsH1 = τ_* ∘
  p_*` with `pull1Cycles_push1Cycles_apply` (the `1+σ` identification,
  pointwise), and the capstone
  `finrank_H1_sub_le_finrank_range_epsH1 : dim H₁(cover) − dim H₁(base)
  ≤ dim (range ε_*)` — i.e. **`E ≥ k̃ − k` for every `XDoubleCoverData`**
  via `BBBocksteinRank.finrank_sub_le_finrank_range_comp`.

**Lean traps hit (recorded for the next phase):** the quotient-level
proof initially died on defeq-but-not-syntactic types
(`D.coverComplex.C1` vs `G × Fin 2`): `rw [map_add]` fails on
mixed-Pi-instance `+`, coercion ascriptions to the native type fail at
reducible transparency, and `binop%` looks *through* type ascriptions, so
one cannot fix a mixed-type `+`/`-` by ascribing operands. Fixes: (a) do
the chase in `BBCover.lean` in native chain types, with `set v' := v +
∂₂ᶜ w'` so every rewrite targets an fvar; (b) in the quotient file,
ascribe coercions to the **ambient** type (`D.coverComplex.C1 → ZMod 2`),
never the native one; (c) express the boundary-witness equality pointwise
(`congrFun` + scalar `ZMod 2` arithmetic, `∀ a b c : ZMod 2, a = b + c →
c = a - b := by decide`) so no Pi instance ever appears; (d) `change`,
never `show`, when moving across the defeq (linter-enforced).

Phase 0 (per-code) only exercises the trivial `E=0` corner on the repo's
actual codes (pair72 is a doubling, `k̃=k`), so it is deprioritized;
Phase 2 (bridge) is unchanged.

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

### Phase 1 — the unconditional inequality `E ≥ k̃ − k` (M–L) — ✅ DONE
Landed in two layers (see Execution status): the instance-agnostic core
(`BBBocksteinRank.lean`, commit `67b947e`) and the homology instantiation
(`BBTransferH1.lean` + `BBCover.lean` chase, 2026-07-04). `epsH1` was
built as `pullH1 ∘ₗ pushH1` (equal to the descended `1+σ` by
`pull1Cycles_push1Cycles_apply`) rather than by descending `deckShift1`
directly — the transfer route hands you exactness for free. The
incl-excl variant sketched below was not needed.

### Phase 2 — the bridge + wiring the element form (M) — ring-side ✅ DONE
**Ring-side composition landed (2026-07-04, `BBEpsFreeGroupAlgebra.lean`
§7, axiom-clean):** `bockstein_element_form_group_algebra` composes L2a
(`epsFree_one_add_single_of_addOrderOf` at `r = 2`) through
`hann_of_epsFree` into L1's `BocksteinLift.bockstein_element_form`, giving
`δ₁δ₂ = 0` **unconditionally at the element level** in `k[G] ⧸ (ε²)` for
every order-4 deck over any char-2 base — the element form now applies to
real Frattini-lift cover rings, not just the single ℤ/4 block L1 hard-coded.
No `MonoidAlgebra ≃ conv` transport was needed for this: the element form is
ring-agnostic and `k[G]` is directly an `AddMonoidAlgebra`, so L2a's
`EpsFree` on `AddMonoidAlgebra k G` feeds it straight in.

**Conv↔group-algebra bridge landed (2026-07-04, `BBConvRing.lean`,
axiom-clean)** — the "standard but verbose" transport of §2.3 decision 2:
- `convEquiv : AddMonoidAlgebra (ZMod 2) G ≃ₗ[ZMod 2] (G → ZMod 2)` —
  the group algebra identified with the repo's function chains.
- `convEquiv_mul` — `convEquiv (a * b) = conv (convEquiv a) (convEquiv b)`:
  the group-algebra **product is the repo's `conv`** (via
  `AddMonoidAlgebra.mul_apply_antidiagonal` over the `{(h, g−h)}`
  antidiagonal).
- `conv_convEquiv_single` — mult by a group generator is a translation
  (`conv (x^s) v = translate (−s) v`); `conv_convEquiv_one_add_single`
  — the deck `ε = 1 + x^σ` acts as `v ↦ v + translate (−σ) v` (the
  repo's `v + σv` for order-2 `σ`).
So L2a's `EpsFree (1 + x^σ)` and the element form now speak, through
`convEquiv`, about the repo's actual chain-level convolution/deck action.

**Remaining (the hard part, NOT wiring):** the homological transport
identifying `bockstein_element_form_group_algebra` with
`BBTransferH1.BocksteinVanishes` (`ker τ_* ≤ range p_*` on `H₁`). With the
ring bridge in hand this reduces to the `seamC`↔connecting-map δ₂
identification (`BBCover.lean:558` `seamC_mem_cycles` is already δ₂ at
chain level): read `cycles / boundaries / H₁` as `convEquiv`-modules
where `∂ᵢ = mul`, so `[u] ∈ ker τ_*` unpacks to an `A z = ε a`,
`B z = ε b` instance the element form kills, placing `[u]` in
`range p_*`. This is the paper's main theorem (the toy free-`D` self-dual
counterexample shows it is *false* for generic 3-term complexes —
liftability, supplied by the order-4 lift behind the element form, is the
content), so it is genuinely open, not plumbing.

### Phase 3 — L2a: `EpsFree` (⟹ `Ann(ε̂) = (ε̂³)`), general — ✅ DONE
Core (`BBEpsFree.lean`): `epsFree_quotXpow` + `epsFree_of_free` +
`hann_of_epsFree`, all axiom-clean.

**The wildcard is CLOSED (2026-07-04, `BBEpsFreeGroupAlgebra.lean`,
axiom-clean):** instead of the two-step "iso `𝔽₂[⟨σ⟩] ≅ 𝔽₂[Y]/(Y^N)` +
subgroup-algebra freeness", one step suffices — `AddMonoidAlgebra k G` is
free **directly over the chain ring** `Λ = AdjoinRoot (X^N : k[X])`,
acting via `AdjoinRoot.lift` with `X ↦ ε = x^σ − 1`:
- `span_transversal_eq_top` — `x^g = mk (C c·(X+1)^j) • x^{t i}` for
  `g = t i + j•σ` (uses `ε + 1 = x^σ` **char-free**, since `ε` is defined
  as `x^σ − 1`, not `1 + x^σ`).
- `linearIndependent_transversal` — canonical `AdjoinRoot.modByMonicHom`
  representatives; the substitution `p ↦ p ∘ (X−1)` turns
  `ε`-polynomials into `x^σ`-polynomials (invertible via `∘ (X+1)`,
  again char-free); coefficient extraction along the orbit
  `t i₀ + m•σ` (`Finsupp`-level, exact order ⟹ orbit points distinct).
- `epsFree_single_sub_one_of_transversal` — the char-free core: any
  `(T, t)` with `(i,j) ↦ t i + j•σ` bijective + `ε^N = 0` gives
  `EpsFree ε N` via `Module.Basis.mk` → `Module.Free.of_basis` →
  `epsFree_of_free ∘ epsFree_adjoinRoot_root`.
- `transversal_out_bijective` — the canonical transversal
  (`Quotient.out` on `G ⧸ zmultiples σ`) for `σ` of exact order `N`.
- `epsFree_one_add_single_of_addOrderOf` — **the deck payoff**: char-2
  base, `addOrderOf σ = 2^r` ⟹ `EpsFree (1 + x^σ) (2^r)` (Frobenius
  `ε^{2^r} = 0` via the instance-free `add_pow_two_pow_of_two_eq_zero`;
  `1 + x^σ = x^σ − 1` in char 2). Works for ANY abelian `G` (finiteness
  not needed) and any char-2 commutative base (`𝔽₂, 𝔽₄, 𝔽₈` blocks
  included). No CRT fallback needed.

### Phase 4 — equality + structure theorem — linear-algebra spine ✅ DONE
**Landed (2026-07-04, axiom-clean).** The equality and its companions are
now Lean theorems, each reduced to the single criterion `BocksteinVanishes`:
- `BBBocksteinRank.finrank_range_comp_add_eq` — the **exact defect
  identity** `E + dim Hb + dim(range p ⊓ ker τ) = dim Hc + dim(ker τ)`,
  purely from exactness `ker p = range τ` (rank-nullity of `τ∘p`, `τ`, and
  `p|_{ker(τ∘p)}`; `map_comap_eq` + `comapSubtypeEquivOfLe`). The
  `range p ⊓ ker τ` term is the entire obstruction.
- `BBBocksteinRank.finrank_range_comp_eq_of_ker_le` — the **tightness
  criterion**: `ker τ ≤ range p → E = dim Hc − dim Hb`.
- `BBTransferH1.BocksteinVanishes D` := `ker pullH1 ≤ range pushH1` — the
  named criterion (= `δ₁∘δ₂ = 0`).
- `BBTransferH1.finrank_range_epsH1_add_eq` / `finrank_range_epsH1_eq` —
  `E + k = k̃` (additive, so `k̃ ≥ k`) / `E = k̃ − k`, under
  `BocksteinVanishes`. **This is `deck_finrank_eq`.**
- `BBTransferH1.finrank_ker_epsH1_eq` — `dim ker ε_* = k` (companion rank).
- `BBTransferH1.epsH1_epsH1_apply` — `ε_*² = 0` (unconditional; from
  `push_*∘pull_* = 0`). Makes `H₁` a `D = 𝔽₂[ε]/(ε²)`-module.

**Remaining for the structure *iso*** `H₁ ≅ D^{k̃−k} ⊕ 𝔽₂^{2k−k̃}`: the
rank data (`E = k̃−k`, `dim ker ε_* = k`, `ε_*²=0`) is all in hand; turning
it into the module iso needs the classification of finitely-generated
modules over `D = 𝔽₂[ε]/(ε²)` (`D^a ⊕ 𝔽₂^b`, not in mathlib) — a separate
algebra task, and it is downstream of `BocksteinVanishes` anyway.

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
| 0 — per-code `native_decide` equality | S–M | no | deprioritized (only trivial `E=0` corner on real codes) |
| 1 — unconditional inequality `E ≥ k̃−k` | M–L | no | **core done** (`BBBocksteinRank`); only the homology instantiation (induced maps + exactness chase) left |
| 2 — bridge + element-form wiring | M | no | not started |
| 3 — L2a general `EpsFree`/`Ann(ε̂)=(ε̂³)` | L | **yes** (no mathlib support) | **core done** (`BBEpsFree`); only coset-basis freeness left |
| 4 — equality + structure thm + write-up | S–M | no | not started |

Full abstract theorem: ≈ 1.5–2.5 weeks, dominated by Phase 3. Pragmatic
milestone (flagship codes + homological inequality, Phases 0–1): ≈ 3–4
days and already a strong, citable result. Not engine-load-bearing (the
doubling program runs at `k̃ = k`); this is the mathematical-core / paper
deliverable, with L1's element form as its foundation.
