# Z3Z6 — parked pending de-nativization

This branch preserves the Z3Z6 instance (`[[36,4,4]] → [[72,4,8]]`, the "pair72"
code) exactly as it stood on `main` at commit 7d8bf6d. It was removed from the
line heading to `main` so that `main` can reach a `native_decide`-free state; this
branch is where the work to bring it back lives.

## Why it was parked

Z3Z6 carries **42 `native_decide` invocations** — more than half of everything
remaining in the repo after the gross `[[144,12,12]]` proof went kernel-only. Five
of them are the expensive ones, each a single `∀ m : Fin (2 ^ 18)` sweep (262,144
base 2-chains, bitmask-encoded) in its own file for build parallelism:

| File | Statement | Role |
|---|---|---|
| `SweepKer.lean` | `bndMask m = 0` and bits 0,1 clear ⟹ `m = 0` | `ker ∂₂` spanning |
| `SweepClassify.lean` | every nonzero boundary of weight ≤ 7 has weight exactly 6, and its coset has a `SeamGood` representative | light-stabilizer classification |
| `SweepSafe01/10/11.lean` | `8 ≤ natWt 36 (seamNNMask ^^^ bndMask m)` | seam-coset floor, one per nonzero seam class |

`native_decide` runs *interpreted*, not compiled, so each of the 262k cases pays
interpreter overhead while evaluating a `bndMask` (an 18-step select-XOR fold) and
a `natWt 36` (a 36-step popcount fold). These five dominate a whole-repo build.

## The route back

The gross conversion (PR #66) established the techniques; two apply here directly.

**`SweepKer` should not be a sweep at all.** Its predicate is F₂-linear in the mask
bits, so it is secretly a rank fact. qec-lab's `docs/lean-patterns.md` Rule 4 covers
exactly this case, and `Z5Z15F2A6/KernelCert.lean` already implements it in this
repo family: a Gaussian-elimination pivot certificate took 560M masks from 53 min
to 3.9 s. The gross proof's `MImClassify.kerBasis_spans` is the same idea in
miniature — a 30-step peeling of the `∂₂` rows, each step reading one row whose
other two cells are already known zero.

**The three `SweepSafe` leaves are harder**, because `natWt` is not linear. They are
minimum-weight-over-a-coset facts, so they need the certificate treatment rather
than a rank argument — the analogue of `SafeFloor/LightFloor.lean`'s `killOK`:
reduce to a small cell frame, take per-cell minima, and kill the tight cells by a
structural link.

**`SweepClassify`** mixes both: a weight claim plus an existential over `SeamGood`
representatives, so expect it to need a witness table alongside the floor argument.

The remaining 37 `native_decide` in this directory are the small ones
(`StabilizerCode` 16, `SeamTables` 6, `Defs` 4, `Witness` 4, `BaseDistance` 3,
`MaskDefs` 3, `SafeFloor` 1) and should convert mechanically with the packing and
bridging tricks: packed-`Nat` tables instead of `Array`/`List` lookups, `mkRing`-style
quantifier bridges so the kernel never whnfs a pi-`Fintype`, and sparse rewrites in
place of `Finset.sum` over the group.

## Restoring

The instance is a clean leaf: nothing outside `Z3Z6/` imports its declarations, and
the only code coupling was one import line in
`QEC/Stabilizer/Codes/BivariateBicycle.lean`. Re-adding it means restoring the
directory, its sibling umbrella `Z3Z6.lean`, that import, and the rows in
`BivariateBicycle/README.md`.
