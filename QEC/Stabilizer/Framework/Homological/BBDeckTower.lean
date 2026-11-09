import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

/-!
# Deck-trivial towers: `σ_* = id` on `H₁` forces `1 + σ ∈ (A, B)`

A bivariate bicycle code with polynomials `A`, `B` over the group algebra
`S = 𝔽₂[G]` has the Koszul complex `S → S² → S` as its chain complex. When `G`
carries a deck transformation `σ` of order `N = 2^r` (a tower of `r` free double
covers), put `ε = 1 + σ`, so that `ε ^ N = 0`. This file proves that if `σ` acts
trivially on `H₁` then `ε` lies in the ideal `(A, B)`; the converse is
`BB.deckTrivial_of_bezout`.

Everything is stated over a commutative ring `S` of characteristic two with
elements `ε A B : S`, the geometry entering through two hypotheses:

- `EpsFree ε N`: an element killed by `ε ^ t` is a multiple of `ε ^ (N - t)`,
  as in a free module over the chain ring `𝔽₂[ε]/(ε ^ N)`;
- `DeckTrivial ε A B`: multiplication by `ε` sends every Koszul 1-cycle to a
  Koszul boundary, i.e. `ε · H₁ = 0`.

The main results are

- `descent`: from `ε ^ t ∈ (A, B)` and `DeckTrivial`, the cycle `ε ^ (N - t) ·
  (f, g)` built from a witness `ε ^ t = f * A + g * B` gives
  `ε ∈ (A, B) + ε ^ (N - t) · S`;
- `iterate`: a tail `ε ^ m · S` with `2 ≤ m` is removed using only `ε ^ N = 0`;
- `eps_mem_of_deckTrivial`: `ε ^ m ∈ (A, B)` for some `2 ≤ m ≤ N - 2` and
  `DeckTrivial` give `ε ∈ (A, B)`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BBDeckTower

variable {S : Type*} [CommRing S]

/-- `ε`-freeness of order `N`: every element killed by `ε ^ t`, `1 ≤ t ≤ N`, is
a multiple of `ε ^ (N - t)`. This is the shape of annihilators in a free module
over the chain ring `𝔽₂[ε]/(ε ^ N)`. -/
def EpsFree (ε : S) (N : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ N → ∀ x : S, ε ^ t * x = 0 → ∃ y : S, x = ε ^ (N - t) * y

/-- `EpsFree` with the order split as `s + t`: an element killed by `ε ^ t` is
a multiple of `ε ^ s`. -/
lemma EpsFree.exists_eq_pow_mul {ε : S} {s t : ℕ} (h : EpsFree ε (s + t)) (ht : 1 ≤ t)
    {x : S} (hx : ε ^ t * x = 0) : ∃ y : S, x = ε ^ s * y := by
  simpa using h t ht (Nat.le_add_left t s) x hx

/-- Deck-triviality on `H₁`: for every Koszul 1-cycle `(y₁, y₂)`, i.e.
`A * y₁ + B * y₂ = 0`, the multiple `ε · (y₁, y₂)` is a Koszul boundary
`(B * z, A * z)`. In characteristic two with `ε = 1 + σ` this says that `σ` acts
as the identity on `H₁`. -/
def DeckTrivial (ε A B : S) : Prop :=
  ∀ y₁ y₂ : S, A * y₁ + B * y₂ = 0 → ∃ z : S, ε * y₁ = B * z ∧ ε * y₂ = A * z

/-- An expression of `ε` modulo `(A, B)` with tail `ε ^ (j + 1) · S` can be
rewritten with the tail `ε ^ (j + 1 + j) · S`. -/
theorem boost (ε A B : S) (j : ℕ)
    (h : ∃ p q v : S, ε = p * A + q * B + ε ^ (j + 1) * v) :
    ∃ p q v : S, ε = p * A + q * B + ε ^ (j + 1 + j) * v := by
  obtain ⟨p, q, v, hpqv⟩ := h
  exact ⟨p + ε ^ j * v * p, q + ε ^ j * v * q, v * v, by
    linear_combination (1 + ε ^ j * v) * hpqv⟩

/-- If `ε ^ N = 0`, an expression `ε = p * A + q * B + ε ^ m * v` with `2 ≤ m`
gives `ε ∈ (A, B)`: each application of `boost` raises the tail exponent, until
the tail vanishes. -/
theorem iterate (ε A B : S) (N : ℕ) (hN : ε ^ N = 0) {m : ℕ} (hm : 2 ≤ m)
    (h : ∃ p q v : S, ε = p * A + q * B + ε ^ m * v) :
    ε ∈ Ideal.span {A, B} := by
  have key : ∀ n, ∃ m', m + n ≤ m' ∧ ∃ p q v : S, ε = p * A + q * B + ε ^ m' * v := by
    intro n
    induction n with
    | zero => exact ⟨m, le_rfl, h⟩
    | succ n ih =>
      obtain ⟨m', hm', h'⟩ := ih
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (show m' ≠ 0 by omega)
      exact ⟨j + 1 + j, by omega, boost ε A B j h'⟩
  obtain ⟨m', hm', p, q, v, h'⟩ := key N
  rw [pow_eq_zero_of_le (by omega) hN, zero_mul, add_zero] at h'
  exact Ideal.mem_span_pair.mpr ⟨p, q, h'.symm⟩

variable [CharP S 2]

/-- The descent step. Given `ε ^ t = f * A + g * B` with `1 ≤ t ≤ N - 1`,
`ε ^ N = 0`, `EpsFree` and `DeckTrivial`, there are `p q v` with
`ε = p * A + q * B + ε ^ (N - t) * v`. The proof applies `DeckTrivial` to the
cycle `ε ^ (N - t) · (f, g)` and divides by powers of `ε` using `EpsFree`. -/
theorem descent (ε A B : S) (N : ℕ) (hN : ε ^ N = 0)
    (hfree : EpsFree ε N) (hR : DeckTrivial ε A B)
    {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ N - 1)
    {f g : S} (hfg : ε ^ t = f * A + g * B) :
    ∃ p q v : S, ε = p * A + q * B + ε ^ (N - t) * v := by
  have two : (2 : S) = 0 := CharTwo.two_eq_zero
  obtain ⟨s, rfl⟩ : ∃ s, N = s + t := ⟨N - t, by omega⟩
  have hfree' : EpsFree ε (t + s) := add_comm s t ▸ hfree
  have hs : 1 ≤ s := by omega
  rw [Nat.add_sub_cancel]
  -- deck-triviality on the cycle `ε ^ s · (f, g)` returns a boundary `(B z, A z)`
  obtain ⟨z, hz1, hz2⟩ := hR (ε ^ s * f) (ε ^ s * g) (by linear_combination hN - ε ^ s * hfg)
  -- `ε ^ t` kills `z`, so `z = ε ^ s * u`
  obtain ⟨u, hu⟩ := hfree.exists_eq_pow_mul h1 (x := z) (by
    linear_combination z * hfg - f * hz2 - g * hz1 + ε * ε ^ s * f * g * two)
  -- `ε ^ s` kills `ε f + B u` and `ε g + A u`, so both are multiples of `ε ^ t`
  obtain ⟨p, hp⟩ := hfree'.exists_eq_pow_mul hs (x := ε * f + B * u) (by
    linear_combination hz1 - B * hu + B * z * two)
  obtain ⟨q, hq⟩ := hfree'.exists_eq_pow_mul hs (x := ε * g + A * u) (by
    linear_combination hz2 - A * hu + A * z * two)
  -- `ε ^ t` kills `ε + (p A + q B)`, which is therefore a multiple of `ε ^ s`
  obtain ⟨v, hv⟩ := hfree.exists_eq_pow_mul h1 (x := ε + (p * A + q * B)) (by
    linear_combination ε * hfg + A * hp + B * hq
      + (ε ^ t * (p * A + q * B) - A * B * u) * two)
  exact ⟨p, q, v, by linear_combination hv - (p * A + q * B) * two⟩

/-- If `ε ^ N = 0`, `ε` is `EpsFree` of order `N` and `DeckTrivial` for `A`,
`B`, then `ε ^ m ∈ (A, B)` for some `2 ≤ m ≤ N - 2` implies `ε ∈ (A, B)`.
For a tower of `r ≥ 2` double covers it is used with `m = 2 ^ (r - 1)`, where
`ε ^ m = 1 + σ ^ m` is the deck element of the top double cover. -/
theorem eps_mem_of_deckTrivial (ε A B : S) (N : ℕ) (hN : ε ^ N = 0)
    (hfree : EpsFree ε N) (hR : DeckTrivial ε A B)
    {m : ℕ} (hm2 : 2 ≤ m) (hmN : m ≤ N - 2)
    (hentry : ε ^ m ∈ Ideal.span {A, B}) :
    ε ∈ Ideal.span {A, B} := by
  obtain ⟨f, g, hfg⟩ := Ideal.mem_span_pair.mp hentry
  exact iterate ε A B N hN (m := N - m) (by omega)
    (descent ε A B N hN hfree hR (by omega) (by omega) hfg.symm)

end BBDeckTower
end Homological
end Stabilizer
end Quantum
