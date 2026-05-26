# Result: Tier 2 round 5 — cover-graph chain-map bound

**Verdict: `shelved-trivial-on-gross`.**

The Symons–Rajput–Browne 2025 cover-graph chain-map bound
([arXiv:2511.13560](https://arxiv.org/abs/2511.13560)) is the first
**non-character-theoretic, non-trivial** lower bound the program has
applied to gross — but it lands at **6**, half the actual `d_gross
= 12`. The structural reason is the §6k obstruction below: gross's
natural cover index is `h = 2`, which is the characteristic of F_2,
so the chain-map injectivity argument loses a factor of 2 in
lower-bound strength.

## Headline numbers

* **Gross [[144, 12, 12]]**: conjectural lower = **6**, rigorous lower
  = **1**, conjectural upper = **12** (tight).
* **Corpus (3894 labeled rows)**: 443 in S (11.4%), **0 violations**
  of the SRB §7 conjecture, 244 rows tight (**55.1% tightness rate**).
* **All 5 Bravyi instances**: bound holds, no violations, no
  tightness. See `evidence.md` § 1.

## Why this is a meaningful program output

Even though shelved, three first-class outputs:

1. **The SRB conjecture passes the lab's largest empirical test.**
   3894 labeled BB instances, 443 in the conjectural fire-zone, 0
   violations. Symons-Rajput-Browne's own paper checks 150 instances
   in Tables 1-10; our sweep is ~3× larger and cross-validates with
   an independently-enumerated corpus. This is published-quality
   corroboration of an open conjecture.

2. **The §6k obstruction articulated.** A new, family-level structural
   limit on cover-graph / chain-map bounds when applied to gross.
   Same arithmetic 2-divisibility that blocks Fourier-transform bounds
   (§6j) blocks chain-map injectivity over F_2 (§6k). For the program,
   this is the same actionable result as §6h-§6j: future Tier-2
   candidates that pass through "linear chain map injective mod char(F)"
   are now flagged a-priori.

3. **A reusable `homological_bounds` module.** ~340 lines of clean
   Python, 27 tests, sub-millisecond bound computation per instance.
   The base-code enumeration, F_2-projection arithmetic, and
   rigorous/conjectural mode discipline are durable for any future
   homological-family candidate.

## Why the bound is loose on gross (the §6k obstruction)

The chain-map argument (SRB Theorems 4.1, 4.3) defines two
F_2-linear maps between cover and base chain complexes:

* **Projection** `p• : Q̃• → Q•` sends each cover monomial to its
  mod-(ℓ', m') image.
* **Lifting** `τ• : Q• → Q̃•` sends each base monomial to the sum of
  its `h = (ℓ̃ · m̃) / (ℓ' · m')` preimage monomials.

The composition `p• ∘ τ•` evaluates to `h · I` on each chain space
(SRB Lemma 4.4). Over F_2, this is

    p• ∘ τ•  =  h · I  =  I   if h is odd
              =  0     if h is even.

For h even, the chain-map composition is the zero map, so it is
**not** the identity, so neither `p•` nor `τ•` is automatically
injective/surjective on homology, so a nonzero base homology class
is no longer guaranteed to lift to a nonzero cover class. The
distance-lift argument breaks.

For gross-as-double-cover-of-[[72, 12, 6]], `h = 2`, this is exactly
the failure regime. SRB's §7 conjecture asserts the bound still
holds (empirically supported), but no proof exists in this
characteristic-divides-cover regime.

The arithmetic of "char(F) divides h" is the same kind of
2-divisibility obstruction that blocks §6j ("2 | |G|" makes F_2[G]
non-semisimple). Different machinery, same arithmetic blocker.
**Whatever produces gross's d = 12 lives in the part of the BB
structure that the F_2-linear cover/chain machinery cannot see in
characteristic 2.**

## What survives if shelved

* `experiments/bb_lab/src/bb_lab/homological_bounds.py` (NEW, 340 LoC).
* `experiments/bb_lab/tests/test_homological_bounds.py` (27 tests).
* `experiments/bb_lab/scripts/tier2_homological_eval.py` (corpus eval
  driver).
* `experiments/bb_lab/notes/T2R5.0_literature.md` (literature triage
  + §6k articulation).
* `experiments/bb_lab/notes/T2R5.3_eval.md` (corpus + Bravyi sweep
  results).
* Full test suite stays at **222 passed, 2 skipped** (was 195
  before, gained 27 new homological tests).

## Proposed §6k obstruction (for HANDOFF.md)

> **§6k. Cover-graph chain-map bounds require h coprime to char(F);
> gross is a 2-cover.**
>
> SRB 2025 (arXiv:2511.13560) gives a per-instance lower bound
> `d_h ≥ d_base` whenever the BB code is an h-fold Tanner-graph cover
> of a smaller BB code, **provided h is odd**. The hypothesis is
> structural: the proof requires `p ∘ τ = h · I` to equal `I` mod 2
> (Lemma 4.4), which holds iff h is odd. Equivalently, the lifting
> chain map τ_• is injective on F_2-homology iff `h ∉ char(F_2) · Z`.
>
> Gross [[144, 12, 12]] is a **double cover (h = 2)** of [[72, 12, 6]]
> (SRB Example 5). The hypothesis fails. The paper conjectures the
> bound still holds for even h based on extensive numerical data, but
> no proof exists for the h-even case.
>
> Implication: under SRB's rigorous theorem, the lower bound on
> `d_gross` is the trivial 1 (no usable base code with h odd). Under
> the empirical conjecture, `d_gross ≥ 6` (from base [[72,12,6]]).
> Neither gets to the target d = 12.
>
> This is the homological analogue of §6j's "2 | |G|" obstruction:
> the same arithmetic 2-divisibility that prevented Fourier-transform
> bounds in §6j now blocks the chain-map injectivity argument. The
> obstruction is family-level, not paper-level: any chain-map
> technique that requires "lifting × projection = identity mod char(F)"
> will be 2-blind on the gross instance.
>
> **Rule for future Tier-2 candidates**: when a homological technique
> requires "h coprime to char(F)" or "lifting map injective mod p",
> verify whether gross falls into the working regime before
> committing. If gross's natural h (the cover index over the relevant
> small base) is even, the bound's value on gross is determined by
> auxiliary structure, not by the primary theorem.

## What was learned, in one paragraph

The categorical separation hoped for in §6j-→-§6k did happen: the
chain-map argument is a true escape from character-theoretic
obstructions, and it produces non-trivial values on gross for the
first time in the program (6 instead of the prior rounds' 1). But
the same arithmetic 2-divisibility that obstructed Fourier methods
(`2 | |G|`) obstructs the chain-map composition over F_2 (`2 | h`).
The lab now knows that the gross code sits at a precise arithmetic
intersection where both major families of distance-bound techniques
lose a factor of 2 — Fourier (factor 2 in semisimple quotient
visibility) and chain-map (factor 2 in lift injectivity). This is
useful: any future bound that promises tightness on gross must
explain how it dodges this 2-divisibility, ahead of implementation,
to avoid burning rounds.

## Recommended next round

If the program continues:

1. **Look for non-natural covers.** SRB Theorem 3.1 only requires
   `π(Ã) = A` axis-wise; an automorphism-twisted version might
   provide an *odd-h* cover that the natural-h=2 cover misses. Highly
   speculative; no theoretical reason to expect one to exist.

2. **Mapping cone / spectral sequence.** SRB §7 remark 8 sketches that
   the mapping cone of `p•` characterizes when h_1(p•) is surjective.
   For h = 2 this cone has non-trivial homology by construction; the
   question is whether its rank governs a quantitative gap between
   `d_base` and `d_cover`. Possible but theoretically new.

3. **Balanced-product distance lemmas** (Breuckmann-Eberhardt 2021).
   BB codes are NOT balanced products in the technical sense, but
   they're close (lifted products over abelian G). Adapting the
   balanced-product distance lower bound to BB might dodge the h=2
   obstruction.

4. **Different chain complex entirely.** The 3-term complex `C_2 →
   C_1 → C_0` is the standard one; a 4- or 5-term complex with
   non-trivial higher homology might admit injectivity arguments that
   survive in characteristic 2.

All of these are real Tier-2 work, not Tier-3. The expected value of
each is low (consistent with the program's empirical history) but
positive (each operates on a genuinely distinct mathematical object,
in the same way this round did vs. character-theoretic rounds).
