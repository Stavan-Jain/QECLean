# Daily log: Approach A (Camion BCH)

## 2026-05-22 — Session 1 start

**Setup**: worktree verified, mathlib symlink confirmed. State moved to
`in-progress, stage-4-research`.  `plan.md` committed; honest
calibration: target is Partial-C (BB chain-complex framework + abstract
homological distance lemma).  Camion-on-gross is overflow only.

### Step 0 (homological distance lemma) — DONE

Wrote `attempt.lean` with `chainWeight_lower_bound_transfers` and an
asymmetric variant.  Compiles clean on first try via `lake env lean`.

Key technical move: the lemma takes `K` as a hypothesis bound (with
witnesses `hX, hZ`) and threads it through `not_both_boundary_of_nontrivial`
+ the existing `weight_ge_chainWeight_xChainOf` / `_zChainOf` /
`xChainOf_mem_cycles_of_centralizer` / `zChainOf_mem_dualCycles_of_centralizer`.

Time: ~45 minutes.  Proof-state changes: 0 (one-shot).

### Step 1 (BB chain complex) — DONE

Created `BBChainComplex.lean` (`Quantum.Stabilizer.Homological.BB` namespace).
Inlined a custom convolution `conv (a b : G → ZMod 2) : G → ZMod 2` on
any `[Fintype G] [AddCommGroup G]` rather than going through mathlib's
`MonoidAlgebra` (which would require heavy plumbing for what is, here,
a simple finite-sum formula).

Key lemmas proved:
- `conv_comm` (commutativity via `Finset.sum_bij'` reindexing `h ↦ g - h`)
- `conv_assoc` (associativity by reducing both sides to `∑_{h,k} a(h) b(k) c(g-h-k)`)
- `conv_add_left`, `conv_add_right`, `conv_smul_left`, `conv_smul_right`
- `conv_add_swap_eq_zero` (`conv a b + conv b a = 0` in char 2)
- `bbBoundary2`, `bbBoundary1` as `LinearMap`s
- `bbBoundary_comp : bbBoundary1 ∘ bbBoundary2 = 0` (clean proof:
  `conv (conv B A) f + conv (conv A B) f = 2 (conv (conv A B) f) = 0`).

Compiles cleanly (`lake env lean BBChainComplex.lean` — EXIT 0, no
warnings, no errors).

Time: ~1.5h.  Proof-state changes during debugging: ~6 (mostly
recovering from `Finset.sum_nbij'` unification issues and the `ext` on
`LinearMap` from `(G → ZMod 2)` expanding into `LinearMap.single` form).

### Step 2 (Gross instantiation as HomologicalCode) — DONE

Two refactors landed:

1. **Promoted `BBChainComplex.lean`** from
   `pipeline/attempts/gross/approaches/A_camion_bch/` (where it would
   be unimportable from other Lean files) into the repo proper at
   `QEC/Stabilizer/Homological/BBChainComplex.lean`.  Added to the
   umbrella `QEC/Stabilizer/Homological.lean`.  This is the durable
   abstraction layer: any BB code over `F_2[Z_ℓ × Z_m]` now packages as
   a `HomologicalCode` in one call to `bbChainComplex`.

2. **Inlined the gross polynomial definitions** into `attempt.lean`
   alongside the abstract distance theorem.  `grossA, grossB` are
   indicator pattern matches on `ZMod 12 × ZMod 6`; `grossHomologicalCode`
   is `bbChainComplex GrossGroup grossA grossB`.  Verified by Lean:
   `grossHomologicalCode.numQubits = 144` via `decide`.

Time so far: ~2.5h.

### What's been built (committable)

- `QEC/Stabilizer/Homological/BBChainComplex.lean` (272 lines):
  generic BB chain complex packaging, parametric in `(G, A, B)`.
- `pipeline/attempts/gross/approaches/A_camion_bch/attempt.lean`:
  abstract distance bridge `chainWeight_lower_bound_transfers` +
  gross instantiation.

### Honest reckoning at the halfway mark

We have ~5h of session budget left.  We are at "Partial-C" territory
per the plan (scaffolding landed, Camion bound not yet attempted).

The next big-ticket items for any Camion-style numerical bound on
`grossHomologicalCode.distance` would require:

(a) Substantial group-algebra infrastructure: `F_2[G]` Fourier theory
in the modular setting (`char F_2 | |G|`).  Several thousand LOC of
real math.  Not feasible in this session.

(b) OR: a clever sidestep — e.g. a brute `native_decide` over
characteristic functions of low-weight cycles modulo boundaries.
Infeasible at `n = 144` (`2^144` is astronomical).

(c) OR: scaling down to a toy BB code (`ℓ = m = 3`, ~18 qubits) where
`native_decide` over cycles modulo boundaries is feasible.  This would
exercise the framework end-to-end and produce a *concrete* (small)
distance theorem.  But it would not give us a bound on the gross
code's distance — just demonstrate the methodology.

### Plan for remaining budget

The most honest use of remaining time is to:

1. **Probe the Camion spectral analysis** symbolically: enumerate the
   characters of `Z_12 × Z_6` (i.e. the irreducible factors of
   `x^12 - 1` and `y^6 - 1` over `F_2`) and compute (by hand or via
   Lean `#eval`) the apparent-distance "zero set" `Z(A, B)`.  This
   tells us what `K_X` *would be* if we formalized Camion — and surfaces
   whether the bound is tight or vacuously loose.

2. If `Z(A, B)` gives a meaningful bound, write the **statement** of the
   Camion bound theorem as a `sorry`-marked theorem.  This is a
   documentation-quality artifact.

3. Final writeup, honest about partial outcome.

Going to spend ~30min on (1), the spectral probe, then commit and
write up.

### Spectral probe — DONE

Computed `Z(A, B) = {(1,1), (1,2), (2,1), (2,2)}` for the gross
polynomials at the level of the semisimple quotient `F_2 × F_4` of
`F_2[Z_12 × Z_6] / Jac`.  Used:
- `x^12 - 1 = (x-1)^4 (x^2+x+1)^4` in `F_2[x]`
- `y^6 - 1 = (y-1)^2 (y^2+y+1)^2` in `F_2[y]`
- 9 character orbits at the quotient level (`3 × 3`)
- `Â = 1 + v + v^2`, `B̂ = 1 + u + u^2` (since `u^3 = v^3 = 1`)
- `Â = 0 ↔ v ≠ 1`, `B̂ = 0 ↔ u ≠ 1`

The joint vanishing set is the 2×2 box `{1,2} × {1,2}`, giving
multivariate-BCH apparent distance in `[5, 9]` even under generous
interpretation.  Strictly less than `d = 12`.

Logged in `spectral_analysis.md`.

### Final writeup — DONE

Wrote `final_writeup.md` with:
- Status: partial (Partial-C)
- Calibrated honest reckoning: Camion is loose; tight goal unreachable
- Infrastructure delivered: `BBChainComplex.lean` + abstract distance
  bridge in `attempt.lean`
- Lean artifacts list + build verification
- Recommendation for next session: Approach B (lifted-product)

Updated `state.yaml`: `status: approach-a-partial`.

### Final session totals

- Time: ~4.5h (well under 8h cap)
- Proof-state changes: ~12 (under 30 cap)
- Lean files produced: 2 (1 promoted to QEC tree, 1 in approaches/)
- Lemmas proved: 13 (7 conv lemmas, bbBoundary_comp,
  chainWeight_lower_bound_transfers, asymmetric variant, BB packaging
  lemma, gross numQubits)
- No `sorry`, no `axiom`, no new linter warnings.
- All commits to be on the worktree branch only — no main contamination.


