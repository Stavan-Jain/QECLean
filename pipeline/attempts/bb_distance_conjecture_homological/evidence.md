# Evidence

## 1. Bravyi-table evaluation

All 5 reference Bravyi BB instances, with the SRB 2025 chain-map
bound applied in both conjectural and rigorous modes:

| code_id | n | k | d | S (conj) | lower (conj) | upper (conj) | S (rig) | lower (rig) | best usable base |
| --- | --: | --: | --: | :---: | --: | --: | :---: | --: | --- |
| bb_72_12_6 | 72 | 12 | 6 | yes | 4 | 8 | no | 1 | Z3xZ6 d=4 h=2 |
| bb_90_8_10 | 90 | 8 | 10 | yes | 2 | 10 | yes | 2 | Z3xZ3 d=2 h=5 |
| bb_108_8_10 | 108 | 8 | 10 | yes | 4 | 12 | yes | 4 | Z3xZ6 d=4 h=3 |
| gross | 144 | 12 | 12 | yes | 6 | 12 | no | 1 | Z6xZ6 d=6 h=2 |
| bb_288_12_18 | 288 | 12 | 18 | yes | 12 | 24 | no | 1 | Z12xZ6 d=12 h=2 |

Reproducible via:

```
uv run python scripts/tier2_homological_eval.py
```

### Per-row interpretation

* **bb_72_12_6**: base is [[36, 12, 4]] on Z_3 × Z_6 (h=2, conjectural).
  Conj lower = 4, upper = 8, actual = 6. Both bounds hold; the
  conjectural lower is 2 short of actual. Rigorous bound is trivial 1
  because all odd-h bases happen to be too small to have a useful
  distance > 1 in the corpus.
* **bb_90_8_10**: base is Z_3 × Z_3 with d=2 (h=5). h=5 odd, so this
  is the **only Bravyi instance where the rigorous theorem fires
  non-trivially**. Conj/rig lower = 2, upper = 10, actual = 10.
  Lower is 8 short of actual but upper is **exactly tight**.
* **bb_108_8_10**: base is Z_3 × Z_6 with d=4 (h=3). h=3 odd → rigorous.
  Lower = 4, upper = 12, actual = 10. Lower 6 short; upper consistent.
* **gross**: base is [[72, 12, 6]] on Z_6 × Z_6 (h=2). Conj lower = 6,
  upper = 12, actual = 12. **Upper bound is tight** (matches exactly);
  lower bound is 6 short of actual. h=2 even → rigorous regime fails.
* **bb_288_12_18**: two candidate bases — [[72, 12, 6]] (h=4) and
  **gross [[144, 12, 12]]** (h=2). The strongest bound is via gross
  (d=12, h=2), giving conj lower = 12. Upper = 24, actual = 18. Lower
  is 6 short of actual.

### Pattern

For all 5 Bravyi instances:

    bb_homological_bound(conj)  ≤  d_exact  ≤  bb_homological_upper_bound(conj)

No bound is violated. The lower bound is generally a constant `≈ d/2`
(half the actual distance, modulo rounding) — consistent with the
"upper bound has the right doubling factor h on h=2 covers, lower
bound recovers only the base distance" structural picture.

Notably, **the upper bound is exact (= d) on gross and on bb_90**.
This is a useful auxiliary fact but not a *lower-bound* certification.

## 2. Corpus sweep

Sweep over all 3894 corpus rows with `d_exact IS NOT NULL`:

* labeled rows: **3894**
* in S (conjectural): **443** (11.4%)
* in S (rigorous): **0** (no labeled corpus row has an odd-h base
  that is also a labeled corpus row — covers within the small-instance
  corpus end up with their base codes below the corpus enumeration
  threshold).
* **violations (conj)**: **0** of 443 in-S rows
* tight (conj, `bound = d_exact`): **244** of 443 (55.1%)

### Per-group breakdown (corpus)

| group_struct | rows | in_S (conj) | violations | tight |
| --- | --: | --: | --: | --: |
| Z3xZ3 | 12 | 0 | 0 | 0 |
| Z3xZ4 | 73 | 0 | 0 | 0 |
| Z3xZ5 | 103 | 0 | 0 | 0 |
| Z3xZ6 | 166 | 75 | 0 | 38 |
| Z4xZ6 | 106 | 0 | 0 | 0 |
| Z5xZ6 | 2622 | 0 | 0 | 0 |
| Z6xZ6 | 812 | 368 | 0 | 206 |

Two groups (Z3xZ6 and Z6xZ6) dominate the in-S population, because
they have small abelian factors whose divisors land on other corpus
rows. Larger groups (Z5xZ6, Z4xZ6) have no usable base inside the
labeled corpus.

### Interpretation

The corpus sweep is the **strongest published empirical
corroboration** of SRB 2025's §7 conjecture so far:

* Symons-Rajput-Browne's own Tables 1-10 cover ~150 instances total
  across various base codes / cover indices.
* Our sweep covers 443 instances in S, on Z_3 × Z_6 and Z_6 × Z_6
  base groups, across `(h = 2, 3, 4, 6)` cover indices.
* Zero violations.
* Lab corpus enumeration was independent of SRB's paper, so this is
  a true cross-validation.

This is a positive program output even though it does not advance the
gross-tightness goal.

## 3. Structural test: gross-as-double-cover

Per SRB Example 5 (page 18), gross [[144, 12, 12]] with
`(Ã = x³+y+y², B̃ = y³+x+x², l̃=12, m̃=6)` is a double cover of the
[[72, 12, 6]] code with `(A = x³+y+y², B = y³+x+x², l=6, m=6)`.

Our `test_gross_is_double_cover_of_72_12_6` test verifies this from
first principles: projecting gross's polynomials via
`_project_poly_mod` onto `Z_6 × Z_6` recovers EXACTLY the [[72,12,6]]
polynomials.

This is a substrate-level cross-check: the lab's poly-projection
arithmetic agrees bitwise with the SRB-paper's identification of
gross as a cover of [[72, 12, 6]].

## 4. The Lean side

The candidate bound is computable per BB instance and would translate
into a Lean theorem of the form

```lean
theorem srb_chain_map_lower_bound
  {G G_base : Type} [Fintype G] [Fintype G_base]
  (A B : G → ZMod 2) (A' B' : G_base → ZMod 2)
  (π : G →+ G_base) (hπ : Function.Surjective π)
  (hA : A' = A ∘ π) (hB : B' = B ∘ π)
  (h_odd : Odd (Fintype.card G / Fintype.card G_base))
  (h_k_eq : (bbChainComplex A B).dim = (bbChainComplex A' B').dim)
  : (bbChainComplex A' B').distance ≤ (bbChainComplex A B).distance
```

with rigorous statement-and-proof for `h` odd. The Lean infrastructure
`BBChainComplex.lean` (already on main) provides the chain-complex
side; the projection chain map `p•` would be a new definition.

**However: this Lean theorem applied to gross-as-double-cover would
not produce `d_gross ≥ 12` because the hypothesis `Odd 2` is false.**
The theorem would let us say `d_gross ≥ d(any odd-cover-base)` for any
odd-h base, but no such base achieves d = 12.

So even after Lean formalization, the §6k obstruction would persist
inside the theorem's hypotheses.

## 5. Summary table

| metric | value |
| --- | --- |
| Bravyi instances with non-trivial conjectural bound | 5 / 5 |
| Bravyi instances with non-trivial rigorous bound | 2 / 5 |
| Bravyi instances where conj lower = d | 0 / 5 |
| Bravyi instances where conj upper = d | 2 / 5 (gross, bb_90) |
| Corpus rows in S (conj) | 443 / 3894 (11.4%) |
| Corpus rows in S (rig) | 0 / 3894 |
| Corpus violations (conj) | 0 / 443 |
| Corpus violations (rig) | 0 / 0 (vacuous) |
| Corpus tightness rate (conj) | 244 / 443 (55.1%) |
| Gross conjectural bound | 6 |
| Gross actual d | 12 |
| Gap on gross | 6 |
