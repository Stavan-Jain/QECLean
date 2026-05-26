# Hypothesis: cover-graph chain-map distance transfer for BB codes

## The candidate bound

Let `Q(A, B, ℓ, m)` be a BB code over `G = Z_ℓ × Z_m` defined by
polynomials `A, B ∈ F_2[G]`. The CSS check matrices
`H_X = (A | B)` and `H_Z^T = (B / A)` define a chain complex

    Q• :    F_2^{ℓm}     →     F_2^{2ℓm}     →     F_2^{ℓm}
            (C_2)         H_Z^T  (C_1)        H_X    (C_0)

whose 1-st homology `H_1(Q•) = ker H_X / im H_Z^T` carries the X-logical
operators (and similarly the Z-side via the dual cochain complex).

Suppose there exists a **base BB code** `Q'(A', B', ℓ', m')` such that
`ℓ' | ℓ`, `m' | m`, and the defining polynomials are related by

    π(A) = A' ∈ F_2[Z_{ℓ'} × Z_{m'}]
    π(B) = B' ∈ F_2[Z_{ℓ'} × Z_{m'}]

where `π : F_2[Z_ℓ × Z_m] → F_2[Z_{ℓ'} × Z_{m'}]` is the F_2-linear
extension of the monomial projection `π(x^a y^b) = x^{a mod ℓ'} y^{b mod m'}`.

Then `Q(A, B, ℓ, m)` is an `h = (ℓ · m) / (ℓ' · m')`-fold cover of
`Q'(A', B', ℓ', m')` (Symons-Rajput-Browne 2025 Theorem 3.1).

The **candidate bound** is:

    d(Q)  ≥  d(Q')                              ... (*)

with two regimes of validity:

* **Rigorous**: holds whenever `h` is odd AND `k_h = k(Q) = k(Q')`
  (SRB Theorem 4.7).
* **Conjectural**: holds for ALL h ≥ 2 (SRB §7 conjecture, page 39).
  No counterexamples reported in SRB's Tables 1-10.

The companion **upper** bound is `d(Q) ≤ h · d(Q')` (SRB Theorem 4.6,
rigorous for h odd; conjectured for all h).

## Why this isn't character-theoretic (escapes §6j)

The proof goes through chain maps `p• : Q̃• → Q•` (projection) and
`τ• : Q• → Q̃•` (lifting) such that `p• ∘ τ• = h · I` on F_2-vector
spaces. The matrices `p_1, τ_1` are concrete F_2-linear maps built
from the cover-projection arithmetic. The argument NEVER references:

* Characters / Pontryagin dual of G.
* Wedderburn decomposition of F_2[G].
* Primitive central idempotents.
* Jacobson radical filtration.
* Fourier transform.

So the §6j obstruction (HANDOFF §6j: F_2[G] non-semisimple when
`2 | |G|`) does not block this approach. **The candidate is categorically
distinct from every previous round's approach.**

## Where the candidate fires non-trivially

Define `S(A, B, G)` to be: "there exists at least one valid base
`(A', B', G')` whose projection from `(A, B, G)` yields a non-trivial
BB code with known distance > 1, satisfying the bound's regime
(rigorous or conjectural)".

For gross [[144, 12, 12]]:
* In conjectural mode: `S` holds (base is [[72, 12, 6]], h = 2,
  d_base = 6).
* In rigorous mode: `S` fails (no odd-h base with known distance > 1
  exists in the literature for gross).

## Expected outcome

Given the analysis in notes/T2R5.0_literature.md §5:

* The lower bound on gross under the conjecture is exactly `d_base
  = 6`. Less than the d ≥ 8 program threshold for "non-trivial enough
  to consider tight". Per the §6h-§6j discipline, this is a
  "**shelved-trivial-on-gross**" outcome.

* The conjecture itself is an interesting object. Verifying that it
  passes across the full BB-lab corpus (~3.9k labeled instances)
  contributes to the program's empirical knowledge even if no Tier-3
  / Tier-4 theorem follows.

* The §6k obstruction (proposed): cover-graph chain-map techniques
  require `gcd(h, char(F_q)) = 1`. Gross-as-double-cover-of-[[72,12,6]]
  has h = 2 = char(F_2), which fails. This pattern likely affects ANY
  cover-graph-based bound on gross, since gross sits at exactly the
  arithmetic where these arguments lose injectivity over F_2.

## What survives if shelved

Whichever way the corpus + Bravyi sweep resolves:

* The `homological_bounds.py` module is a clean, well-tested
  implementation of the SRB 2025 cover-graph projection and bound,
  with both rigorous and conjectural modes properly distinguished.
  Future Tier-2 candidates that need to enumerate base codes (e.g.
  for the §6k-articulating obstruction or for an extension to
  characteristic-2 chain maps) can build on this.

* The §6k obstruction (if articulated) becomes a permanent program
  invariant: any future moonshot that proposes a bound on gross via
  "chain map cover→base injectivity over F_2" has to dodge h = 2
  somehow.

## Operational definition of the bound

```python
from bb_lab.homological_bounds import bb_homological_bound

# Conjectural mode (any h):
lower = bb_homological_bound(A, B, G, base_distance=lookup_fn)

# Rigorous mode (SRB Theorem 4.7, h odd & k_h = k):
lower_rig = bb_homological_bound(
    A, B, G, base_distance=lookup_fn, require_rigorous=True
)
```

The `lookup_fn(A', B', G') → int | None` callable resolves base
distances; the Bravyi table is the primary lookup, the corpus DB is
the secondary.

## Falsification criterion

The candidate is **falsified** if any corpus row with `d_exact IS NOT
NULL` has `bb_homological_bound > d_exact` (the lower bound exceeds
the exact distance). This would mean the SRB §7 conjecture is wrong
on at least one instance — a publishable result independent of the
gross-tightness question.

The candidate is **shelved-trivial-on-gross** if the bound's value on
gross is ≤ 8 (the §6h-§6j threshold). At a literature-known maximum
bound of 6 (= d([[72, 12, 6]])) under the natural h=2 cover, this is
the a-priori expected outcome.
