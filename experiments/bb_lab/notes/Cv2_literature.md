# C-v2 — literature check for the radical-weight distance bound

Date: 2026-05-26.

Companion to [Cv1_literature.md](Cv1_literature.md). The C-v1 lit pass
established the literature gap that lets `w_μ` exist as a novel
invariant. This pass checks whether the C-v2 conjecture's SHAPE
(radical-weight numerator divided by LP-style `c`) appears anywhere.

## 1. The C-v2 conjecture's shape

```
d_X(BB(G, A, B))  ≥  (1/c) · min_O min(w_1(A, O), w_1(B, O)),
                     c = [G_a : G_a ∩ G_b].
```

The shape is parallel to Lin–Pryadko Statement 12, with the C-v1
quantity `w_1` replacing the classical `d_A^⊥`.

## 2. Adjacent prior work re-checked

- **Berman 1967 / Charpin 1988 / Andriatahiny 2016
  ([arXiv:1601.07633](https://arxiv.org/abs/1601.07633),
  [arXiv:1609.09531](https://arxiv.org/abs/1609.09531))**: as noted in
  [Cv1_literature.md](Cv1_literature.md), these give min-weight of
  `rad^μ(F_p[G])` for elementary abelian p-groups. Their min-weight
  invariant is unrelated to ANY denominator structure — it's just
  `min |·|_H` over the radical power as a code. **No LP-style
  composition appears in these papers.**

- **Lin–Pryadko 2023 ([arXiv:2306.16400](https://arxiv.org/abs/2306.16400))
  Statement 12**: `d ≥ ⌈d_A^⊥ / c⌉` with `c = |G_a ∩ G_b|`.
  - Note: the LP paper uses `c = |G_a ∩ G_b|` as the divisor (subgroup
    *order*), while HANDOFF_C2 specified `c = [G_a : G_a ∩ G_b]`
    (subgroup *index*). For gross both happen to equal 3, but the
    distinction matters for the corpus sweep. **C-v2 uses
    `c = [G_a : G_a ∩ G_b]` per HANDOFF_C2.**
  - The LP numerator is `d_A^⊥` (a classical-dual-distance quantity).
    Substituting `w_1` (the C-v1 radical-aware quantity) is what makes
    C-v2 a candidate novel result.

- **Jitman–Ling 2013 (TIT 59(5))**: distance bounds in non-semisimple
  PIGAs transfer through the semisimple quotient and are never
  sharper. The C-v2 conjecture's numerator `w_1` is constructed
  precisely on the non-semisimple structure that JL prove transfers
  away — so by JL, no closed-form lower bound using only
  semisimple-quotient quantities can match `w_1` on gross. The C-v2
  conjecture *would*, if it held, evade JL's barrier. (It does not
  hold; see [Cv2_corpus_sweep.md](Cv2_corpus_sweep.md) and
  [Cv2_bravyi_table.md](Cv2_bravyi_table.md).)

- **Wang–Mueller 2024 *Coprime Bivariate Bicycle Codes*
  ([arXiv:2408.10001](https://arxiv.org/abs/2408.10001))**: closed
  upper bounds for `coprime` BB codes (codes with `gcd(ℓ, m) = 1`).
  Restricted to coprime case; not the gross-style domain.

- **Symons–Rajput–Browne 2025
  ([arXiv:2511.13560](https://arxiv.org/abs/2511.13560))**: BB-cover
  bounds — out of scope per HANDOFF.md §6k (2-divisibility wall).

- **Bernal–Bueno-Carreño–Simón 2016
  ([arXiv:2402.03938](https://arxiv.org/abs/2402.03938))**: B-apparent
  distance refinements. Semisimple-only.

## 3. Search queries (May 2026)

- `"Loewy weight" "minimum distance" quantum code lower bound radical`
  — no hits in coding theory; mostly Loewy series in representation
  theory (unrelated).
- `"radical filtration" "minimum distance" cyclic code lower bound denominator coset`
  — finds Hartmann–Tzeng / Roos generalizations on the classical
  cyclic side, none composing with a non-semisimple denominator.
- `Lin Pryadko 2-block group algebra distance lower bound radical augmentation`
  — confirms LP 2023 is the closest published bound (
  [arXiv:2306.16400](https://arxiv.org/abs/2306.16400)).

## 4. Verdict

The conjecture's *shape* is well-known (LP Stmt 12). The *numerator*
substituted (`w_1` from C-v1) does not appear in any published
LP-style composition. The combination is plausibly novel — IF it
holds. The corpus sweep proves it does not (see
[Cv2_corpus_sweep.md](Cv2_corpus_sweep.md)), so the lit check is
mooted by the falsification.

## References

- LP 2023 — [arXiv:2306.16400](https://arxiv.org/abs/2306.16400).
- Jitman–Ling — IEEE TIT 59(5) (2013), 3046–3058.
- Berman 1967, Charpin 1988, Andriatahiny 2016 — see
  [Cv1_literature.md](Cv1_literature.md).
- Wang–Mueller 2024 — [arXiv:2408.10001](https://arxiv.org/abs/2408.10001).
