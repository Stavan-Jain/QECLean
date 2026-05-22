# Approach A: Camion multivariate BCH bound — plan

## Setup and goal

For a CSS code with check matrices `H_X = [A | B]`, `H_Z = [B^T | A^T]` over
`F_2[Z_ℓ × Z_m]`, distance is:

```
d = min { wt(c) : c ∈ ker H_X \ im H_Z^T } ⊓
    min { c ∈ ker H_Z \ im H_X^T }
```

We want a lower bound `d ≥ K` from spectral analysis of the polynomial
pair.

The existing `Stabilizer/Homological/` framework gives us
**`not_both_boundary_of_nontrivial`**: every nontrivial logical
`g : NQubitPauliGroupElement` has `xChainOf g ∉ boundaries` OR
`zChainOf g ∉ dualBoundaries`. Combined with
`weight_ge_chainWeight_xChainOf` (and Z-mirror), the distance reduces to:

```
d ≥ min(K_X, K_Z)
where  K_X = min { chainWeight c : c ∈ cycles \ boundaries }
       K_Z = min { chainWeight c : c ∈ dualCycles \ dualBoundaries }
```

So Approach A's job is: **produce a Lean theorem giving a lower bound on
`K_X` (and `K_Z`)** for the BB-code chain complex built from `(A, B)`.

## Camion's recipe (specialized for our setting)

Classical Camion (Bernal-Simón 2024 reformulation):

Let `C ⊆ F_2[G]` be an ideal (= a `G`-invariant linear code).  Then over
the algebraic closure `F_2-bar`, by the structure theorem,
`F_2-bar[G] ≅ ∏_χ F_2-bar` (1D pieces per character `χ`).  Each codeword
`c` decomposes spectrally:  `c = ∑_χ ĉ(χ) χ`, with `ĉ : Ĝ → F_2-bar`.

The **apparent distance** is the smallest weight (in `G`) of any
nonzero function `c : G → F_2-bar` such that `ĉ` vanishes on a chosen
"defining set" `Z ⊆ Ĝ`.  When `Z` contains a "consecutive zero pattern"
in the lex order on `Ĝ ≅ Z_ℓ × Z_m`, classical Camion shows
`wt(c) ≥ |consecutive run| + 1`, generalizing BCH.

### Adapting to CSS (the novel piece)

For a BB code, the X-cycles are `ker_F_2 [A | B]` viewed as a subspace of
`F_2[G]² = F_2[G] ⊕ F_2[G]`.  As a `G`-module, this kernel is
`G`-invariant, so it's a sum of isotypic components indexed by `Ĝ`.
The Camion analysis becomes:  for each character `χ`, the `χ`-isotypic
component of `ker[A|B]` is the kernel of the 1×2 matrix `[Â(χ), B̂(χ)]`
over `F_2(χ)`.  That kernel is nonzero iff `Â(χ) = B̂(χ) = 0`.  Similarly,
the `χ`-isotypic component of `im H_Z^T = im [B^T; A^T]` is the image of
`[B̂(χ); Â(χ)]^T`, which equals the kernel exactly when at least one of
`Â(χ), B̂(χ)` is nonzero.

So the `χ`-isotypic component of the **quotient** `ker H_X / im H_Z^T`
is nonzero iff both `Â(χ) = B̂(χ) = 0`.  Define

```
Z(A, B) := { χ ∈ Ĝ : Â(χ) = 0 ∧ B̂(χ) = 0 }
```

Then a non-boundary X-cycle is a function whose Fourier transform is
**zero outside `Z(A, B)`**.  The Camion-style apparent distance is the
*classical apparent distance of the cyclic code with defining set
`Ĝ \ Z(A, B)`*.

### Char-2 / modular obstacle

Because `char F_2 = 2 | |G| = 72`, the algebra `F_2-bar[G]` does not
literally decompose as `∏_χ F_2-bar`.  Instead, one works over `F_2`
directly with the CRT decomposition

```
F_2[Z_ℓ] = ∏_i F_2[x]/(f_i(x))
```

where `f_i` are the irreducible factors of `x^ℓ - 1` over `F_2`.  Over
`F_2`, `x^12 - 1 = (x-1)^4 · (x^2 + x + 1)^4` (since 12 = 4 · 3 and
`x^3 - 1 = (x-1)(x^2+x+1)` over `F_2`, and we get the 4th power from
the 4 = 2^2 part).  Wait — this is wrong; let me redo:
`x^12 - 1 = (x^3)^4 - 1 = ((x^3 - 1))^4` only if char dividing the
exponent — yes, in `F_2`, `x^12 - 1 = (x^3 - 1)^4 = ((x-1)(x^2+x+1))^4`.

So `F_2[x]/(x^12-1)` has nilpotents — it's NOT a product of fields.
Likewise `F_2[y]/(y^6-1) = F_2[y]/((y-1)^2 (y^2+y+1)^2)`.

**For Camion: we'll work in the semisimple quotient** `F_2[x]/(x^12-1) /
nilrad = F_2[x]/((x-1)(x^2+x+1)) ≅ F_2 × F_4` — there are exactly **2
characters of `Z_12`** that survive modular reduction (the trivial char
sending `x ↦ 1`, and the nontrivial char of `Z_3` sending `x ↦ ω`).
Plus their products with the `Z_6` characters, also modular-reduced.

Total distinct characters surviving:
- `Z_12 / (x-1)·(x^2+x+1)` part has `1 + 2 = 3` characters: `χ_0 (x ↦ 1)`,
  `χ_1 (x ↦ ω)`, `χ_2 (x ↦ ω^2)` where `ω ∈ F_4 \ F_2`.
- `Z_6 / (y-1)·(y^2+y+1)` part has `1 + 2 = 3` characters: `ψ_0, ψ_1, ψ_2`.
- Total: `3 × 3 = 9` characters over `F_4` (or `F_16` to accommodate the
  product).

This is small enough to **enumerate by hand**.

### Computing `Z(A, B)` for the gross polynomials

`A = x^3 + y + y^2`, `B = y^3 + x + x^2`.

Over each character `(χ_i, ψ_j)`:
- `χ_0, ψ_0` (trivial): `Â = 1 + 1 + 1 = 1 ≠ 0`, `B̂ = 1 + 1 + 1 = 1 ≠ 0`.
  Not in `Z(A,B)`.
- `χ_1, ψ_0` (x ↦ ω, y ↦ 1): `Â = ω^3 + 1 + 1 = ω^3`; over `F_4`, `ω^3 = 1`
  so `Â = 1 ≠ 0`. Not in `Z(A,B)`.
- `χ_0, ψ_1`: `Â = 1 + ψ + ψ^2 = 1 + ω + ω^2 = 1 + 1 = 0` (since
  `ω + ω^2 = 1` in `F_4`). Need to also check `B̂`:
  `B̂ = ψ^3 + 1 + 1 = ψ^3 = 1`. So `B̂ ≠ 0`. Not in `Z(A,B)`.

Continuing through all 9 characters, we need to find the subset where
both Â and B̂ vanish. Given the structure (Â involves `x^3` plus
`y + y^2`, etc.), the analysis is mechanical.

**This is the key computation. If `Z(A, B) = ∅` (other than possibly
the trivial char), then `ker H_X / im H_Z^T = 0` — implying `k = 0`,
which CONTRADICTS the known `k = 12`. So `Z(A, B)` must be nonempty.**

Actually wait — we should expect `|Z(A,B)| ≈ k/2 = 6` characters
(since each nontrivial isotypic component contributes some logical
qubits). For `k = 12` and the dimensional structure, this is consistent.

### Apparent-distance lower bound

Once we know `Z(A, B)`, the Camion apparent distance is:

```
d_app = max consecutive-zero pattern length in (Ĝ \ Z(A,B))
        viewed cyclically + 1
```

For the modular case, the right notion involves *cyclotomic cosets*
rather than single characters, but the principle is the same.

## Plan — concrete intermediate lemmas

Given the 8h session budget and the scope of the math above, here is a
realistic ordering of work, **starting from the bottom up to first hit
compiling Lean**.

### Step 0: Stage compiling skeleton (target: 1h)

Create `pipeline/attempts/gross/approaches/A_camion_bch/attempt.lean`
with:
- Imports for `Stabilizer/Homological/Distance.lean`
- Statement of the abstract theorem template:
  `∀ K, (∀ c ∈ X.cycles \ X.boundaries, K ≤ X.chainWeight c) →
       (∀ c ∈ X.dualCycles \ X.dualBoundaries, K ≤ X.chainWeight c) →
       ∀ g nontrivial, K ≤ NQubitPauliGroupElement.weight g`
- This is a **pure homological lemma**, requires no group-algebra work.
  It says: a chain-weight lower bound transfers to a Pauli weight lower
  bound for any homological CSS code.

This is the **first deliverable** — concrete, achievable, and the
necessary scaffold for any Camion-style application.

### Step 1: BB chain complex setup (target: 1.5h)

Define a concrete `HomologicalCode` instance for a BB code given
`(ℓ, m, A, B)` where `A, B` are functions `Fin ℓ × Fin m → ZMod 2`
(coefficient vectors of polynomials over `F_2[Z_ℓ × Z_m]`).

Cells:
- `C0 := Fin ℓ × Fin m` (1 per group element, "vertex" / Z-stabilizer)
- `C1 := (Fin ℓ × Fin m) × Fin 2` (2 per group element, indexed by L/R
  block; "edge" / qubit)
- `C2 := Fin ℓ × Fin m` (1 per group element, "face" / X-stabilizer)

Boundary maps (chains as `ZMod 2`-valued functions):
- `∂₁ : (C1 → ZMod 2) → (C0 → ZMod 2)` defined by `H_Z = [B^T | A^T]`:
  `∂₁(c)(g) = (B^T · c_L + A^T · c_R)(g)` where `c_L, c_R` are the
  two halves and `·` is group-algebra mult.
- `∂₂ : (C2 → ZMod 2) → (C1 → ZMod 2)` defined by `H_X^T = [A^T; B^T]`:
  `∂₂(f)(g, 0) = (A · f)(g)`,  `∂₂(f)(g, 1) = (B · f)(g)`.

This is just the standard CSS-to-chain-complex bridge — the
**chain-complex law** `∂₁ ∘ ∂₂ = 0` reduces to `[B^T | A^T] · [A; B] =
B^T A + A^T B = 0` over `F_2`, which holds because `A, B` commute in
`F_2[G]` (`G` abelian), and `B^T A = AB`, `A^T B = BA`, so their sum is
`AB + BA = 2AB = 0` in char 2. **Clean.**

### Step 2: Gross instantiation (target: 1h)

Define `grossA, grossB : Fin 12 × Fin 6 → ZMod 2` as the indicator
functions of `{(3,0), (0,1), (0,2)}` and `{(0,3), (1,0), (2,0)}`
respectively. Plumb into the BB chain complex.

### Step 3: Honest reckoning — what's left for "Camion" itself?

To get a numerical `K_X ≥ k` lower bound, we still need to **execute the
Fourier / spectral analysis**.  At this point we're well into the
mathematical work where the literature gap lives.

Options to triage at Step 3:

**Option 3a (cleanest scope-cut): mechanical `native_decide` bound.**
For the specific Gross polynomials, the predicate `chainWeight c ≥ K`
on `cycles \ boundaries` is a decidable property over the finite set
`C1 → ZMod 2 = (ZMod 2)^144`.  But `2^144 ≈ 10^43` — **way too large to
decide directly**.  No-go.

**Option 3b (toy-case Lean): scale down to `[[18, ?, ?]]` or
`[[50, ?, ?]]` BB code.**  Build the Camion machinery on a small BB
code (e.g. `ℓ = m = 3`, polynomials chosen so we can `native_decide`).
This gives us a working Camion-Lean theorem **at small scale**, but
doesn't address the gross code directly.  Still a partial result.

**Option 3c (parametric Camion theorem in Lean): the real work.**
Write the Camion apparent-distance theorem parametrically — i.e. for any
abelian `G`, polynomial pair `(A, B)`, define `Z(A, B)` symbolically,
and prove `K_X ≥ d_app(Z(A,B))`.  This is the high-effort path; needs
substantial group-algebra infrastructure (`F_2[G]`, characters in the
modular setting).  Realistically a 30+ hour endeavor, well beyond a
single session.

**Realistic session goal** (given 8h cap and infrastructure cost): land
Steps 0, 1, 2 cleanly compiling.  This produces:

1. A pure homological lemma `homological_distance_ge_of_chainWeight_bounds`
   showing how chain-weight bounds yield distance lower bounds.
2. A `BBChainComplex` definition for arbitrary `(ℓ, m, A, B)` over
   `F_2[Z_ℓ × Z_m]`, with the boundary-comp-zero proof.
3. `grossA, grossB` instantiations + a `grossChainComplex : HomologicalCode`
   definition.

This is **honest partial value**.  It's *not* a Camion bound — it's
the **scaffolding** required for a Camion bound, plus the homological
distance bridge that converts chain-weight bounds to Pauli-weight
bounds.  The Camion bound itself is then a TODO.

### Step 4: If time permits, attempt Camion on a toy BB code

After Steps 0-2 are committed and compiling, if there's >2h of budget
remaining, attempt Step 3b: instantiate a `[[18, k, d]]`-style toy BB
code (ℓ = m = 3, sparse polynomials).  Compute `k`, `d` by `native_decide`
where feasible.  Use the homological theorem from Step 0 to convert.

If `native_decide` is too slow even on `[[18, ?, ?]]` (`2^18 ≈ 260k`
states for X-cycles, manageable), use it.  Otherwise, scale further down
to `[[8, ?, ?]]`.

### Step 5: Final writeup (mandatory, regardless of partial outcome)

Write `final_writeup.md` with:
- Status (likely "partial" — infrastructure landed, Camion-on-gross not
  reached)
- What was built (the homological lemma, BB chain complex, gross
  instantiation)
- What wasn't (Camion's actual apparent-distance bound, the spectral
  analysis itself)
- Whether the obstacle is fundamental or surmountable (surmountable —
  it's "more work", not "blocked")
- Recommended Approach B input: with the BBChainComplex landed, the
  lifted-product / Tillich-Zémor route has a starting point.

## Honest probability re-calibration

Given the work involved:

- **Tight (`d ≥ 12` in Lean)**: < 1% in this session. Would need a
  Camion-on-gross spectral analysis + Lean proof, both novel.
- **Partial-A (parametric Camion + numerical bound on gross)**: < 5%
  this session — requires the spectral analysis which is itself
  significant new math.
- **Partial-B (classical Camion + CSS extension sketch)**: 10-15% this
  session — also requires the classical Camion proof.
- **Partial-C (just the BB chain-complex framework + homological
  distance lemma, no Camion yet)**: 60% this session.  This is the
  **realistic target**.
- **Negative result**: 20% — we hit an obstacle in the BB chain-complex
  construction itself (e.g. an HMul mismatch in the modular ring) and
  write up the obstacle.

## Stop criteria checklist

- [ ] 8h session wall-clock
- [ ] 30 proof-state changes
- [ ] 60min no-progress window
- [ ] After Step 5 writeup, stop regardless

We will explicitly **not** spawn Approach B in this session.
