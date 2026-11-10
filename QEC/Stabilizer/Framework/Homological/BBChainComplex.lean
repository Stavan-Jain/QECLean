import QEC.Stabilizer.Framework.Homological.Distance

/-!
# The bivariate bicycle chain complex

A bivariate bicycle (BB) code is a CSS code built from two elements `A`, `B` of
the group algebra `𝔽₂[G]` of a finite abelian group `G`; for
`G = ZMod ℓ × ZMod m` this is `𝔽₂[x, y] / (xˡ - 1, yᵐ - 1)`. An element of
`𝔽₂[G]` is written as a function `G → ZMod 2` and the product is the
convolution `conv`. The code has two blocks of `|G|` qubits, so its 1-cells are
`G × Fin 2`, and its chain complex is

* `∂₂ f = (A ⋆ f | B ⋆ f)` on 2-chains `f : G → ZMod 2` (one X-check per
  group element),
* `∂₁ c = B ⋆ c_L + A ⋆ c_R` on 1-chains with halves `c_L`, `c_R` (one Z-check
  per group element).

The chain-complex law `∂₁ ∘ ∂₂ = 0` is `B ⋆ A + A ⋆ B = 0`, which holds because
convolution is commutative and the coefficients have characteristic 2. In
matrix terms, writing `M_a` for the matrix with entries `M_a f h = a (h - f)`,
the X-check matrix is `[M_A | M_B]` and the Z-check matrix is `[M_Bᵀ | M_Aᵀ]`.

## Main definitions

* `conv a b`, with the scoped infix `a ⋆ b`: convolution on `G → ZMod 2`, a
  commutative, associative, bilinear product (`conv_comm`, `conv_assoc`,
  `conv_add_left`, `conv_smul_left`, …) for which point masses act by
  translation (`conv_single_left`).
* `poly[x^3 + y + y^2]`: scoped literal for an element of
  `𝔽₂[ZMod ℓ × ZMod m]` given by its monomials.
* `translate`, `translate1`: translation of chains by a group element, which
  commutes with the boundary maps (`bbBoundary1Fn_translate1`,
  `bbBoundary2Fn_translate`).
* `leftHalf`, `rightHalf`: the two blocks of a 1-chain (`halves_ext_iff`).
* `bbBoundary1Fn`, `bbBoundary2Fn`: the boundary maps as plain functions, and
  `bbBoundary1`, `bbBoundary2`: the same maps as `ZMod 2`-linear maps, with
  `bbBoundary_comp : ∂₁ ∘ ∂₂ = 0`.
* `bbChainComplex A B : HomologicalCode`: the chain complex, on
  `bbNumQubits G = 2 * |G|` qubits.
-/

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Convolution on a finite abelian group -/

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- Convolution of two `ZMod 2`-valued functions on a finite abelian group `G`:
`(a ⋆ b) g = ∑ h, a h * b (g - h)`. This is the product of the group algebra
`𝔽₂[G]`. -/
def conv (a b : G → ZMod 2) : G → ZMod 2 :=
  fun g => ∑ h : G, a h * b (g - h)

/-- `a ⋆ b` is the convolution `conv a b` (the group-algebra product of
`𝔽₂[G]`). Scoped to `Quantum.Stabilizer.Homological.BB`: active inside that
namespace, and elsewhere under `open scoped Quantum.Stabilizer.Homological.BB`.
Multiplicative precedence (`70`), so `(a ⋆ b) g` needs its parentheses and
`a ⋆ b + c` does not. The `simp`/`rw`/`unfold` lists keep the bare name `conv`.
-/
scoped infixl:70 " ⋆ " => conv

section PolyNotation

open Lean

/-! ### Polynomial literals

The polynomials `A`, `B` of a bivariate bicycle code are `ZMod 2`-valued
indicator functions on `G = ZMod ℓ × ZMod m`, the monomial `xᵃyᵇ` standing for
the point `(a, b)`. `poly[x^3 + y + y^2]` writes such a function as a sum of
monomials and expands to exactly

```lean
fun g => if g = (3, 0) ∨ g = (0, 1) ∨ g = (0, 2) then 1 else 0
```

(the monomials in the written order, `∨` nested to the right as usual), a form
that kernel `decide` evaluates. Monomials are `1`, `x`, `y`, `x^i`,
`y^j`, `x^i*y^j` (with `x*y^j`, `x^i*y`, `x*y` for exponent `1`). Scoped like
`⋆`. -/

declare_syntax_cat bbPoly (behavior := both)

/-- The constant monomial `1` (the point `(0, 0)`); other numerals are rejected.
-/
scoped syntax num : bbPoly
/-- The monomial `x` or `x^i` (the point `(i, 0)`). -/
scoped syntax &"x" ("^" num)? : bbPoly
/-- The monomial `y` or `y^j` (the point `(0, j)`). -/
scoped syntax &"y" ("^" num)? : bbPoly
/-- The monomial `x^i*y^j` (the point `(i, j)`), either exponent optional. -/
scoped syntax &"x" ("^" num)? "*" &"y" ("^" num)? : bbPoly
/-- Polynomial sum, left-associative. -/
scoped syntax:65 bbPoly:65 " + " bbPoly:66 : bbPoly

/-- `poly[x^3 + y + y^2]` is the indicator function
`fun g => if g = (3, 0) ∨ g = (0, 1) ∨ g = (0, 2) then 1 else 0` of the
monomials' exponent points, for use as a bivariate-bicycle polynomial
`G → ZMod 2`. Scoped to `Quantum.Stabilizer.Homological.BB`.

The `+` is a union of *distinct* exponent points, not addition in `𝔽₂[G]`: the
literal is the polynomial it spells only when the written monomials are pairwise
distinct modulo the group orders. A syntactically repeated monomial is rejected,
but a coincidence modulo the orders cannot be seen at macro time —
`poly[1 + x^6]` is `1 + x⁶` over `ZMod 12 × ZMod 6` but the constant `1` (not
`0`) over `ZMod 6 × ZMod 6` — so check the exponents against the intended group.
There is no literal for the zero polynomial; write `0`. -/
scoped syntax:max (name := polyLit) "poly[" bbPoly "]" : term

/-- The exponent points `(a, b)` of a `bbPoly` sum, in the written order. -/
partial def monomialsOf : TSyntax `bbPoly → MacroM (List (Nat × Nat))
  | `(bbPoly| $p + $q) => do return (← monomialsOf p) ++ (← monomialsOf q)
  | `(bbPoly| $n:num) =>
    if n.getNat == 1 then return [(0, 0)]
    else Macro.throwErrorAt n "expected the monomial 1"
  | `(bbPoly| x) => return [(1, 0)]
  | `(bbPoly| x ^ $a:num) => return [(a.getNat, 0)]
  | `(bbPoly| y) => return [(0, 1)]
  | `(bbPoly| y ^ $b:num) => return [(0, b.getNat)]
  | `(bbPoly| x * y) => return [(1, 1)]
  | `(bbPoly| x ^ $a:num * y) => return [(a.getNat, 1)]
  | `(bbPoly| x * y ^ $b:num) => return [(1, b.getNat)]
  | `(bbPoly| x ^ $a:num * y ^ $b:num) => return [(a.getNat, b.getNat)]
  | stx => Macro.throwErrorAt stx "expected a monomial 1, x^i, y^j, or x^i*y^j"

macro_rules
  | `(poly[$p]) => do
    let mons ← monomialsOf p
    if let some d := mons.find? fun m => mons.count m > 1 then
      Macro.throwErrorAt p
        s!"repeated monomial x^{d.1}*y^{d.2}: `+` in `poly[…]` is a union of distinct points"
    let g := mkIdent `g
    let some (last, init) := mons.getLast?.map fun l => (l, mons.dropLast) | Macro.throwUnsupported
    let mkEq : Nat × Nat → MacroM Term := fun (a, b) =>
      `($g = ($(quote a), $(quote b)))
    let mut disj : Term ← mkEq last
    for m in init.reverse do
      disj ← `($(← mkEq m) ∨ $disj)
    `(fun $g => if $disj then 1 else 0)

section PolyDelab

open PrettyPrinter Delaborator SubExpr

/-- A literal natural number: a raw literal or the `OfNat.ofNat` form numerals
elaborate to. -/
private def numeral? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal k) => some k
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal k) => some k
      | _ => none
    else none

/-- The exponent point of the disjunct `g = (a, b)` with `g` the loose bound
variable `0` and literal `a`, `b`. -/
private def exponentPoint? (e : Expr) : Option (Nat × Nat) := do
  guard (e.isAppOfArity ``Eq 3)
  guard (e.getArg! 1 == .bvar 0)
  let pt := e.getArg! 2
  guard (pt.isAppOfArity ``Prod.mk 4)
  let a ← numeral? (pt.getArg! 2)
  let b ← numeral? (pt.getArg! 3)
  return (a, b)

/-- The exponent points of a right-nested `∨` chain of such disjuncts. -/
private partial def exponentPoints? (e : Expr) : Option (List (Nat × Nat)) :=
  if e.isAppOfArity ``Or 2 then do
    let m ← exponentPoint? (e.getArg! 0)
    let ms ← exponentPoints? (e.getArg! 1)
    return m :: ms
  else
    (exponentPoint? e).map ([·])

/-- The `bbPoly` monomial for an exponent point. -/
private def monomialSyntax (m : Nat × Nat) : DelabM (TSyntax `bbPoly) := do
  let lit (k : Nat) : TSyntax `num := Syntax.mkNumLit (toString k)
  match m with
  | (0, 0) => `(bbPoly| 1)
  | (1, 0) => `(bbPoly| x)
  | (a, 0) => `(bbPoly| x ^ $(lit a))
  | (0, 1) => `(bbPoly| y)
  | (0, b) => `(bbPoly| y ^ $(lit b))
  | (1, 1) => `(bbPoly| x * y)
  | (a, 1) => `(bbPoly| x ^ $(lit a) * y)
  | (1, b) => `(bbPoly| x * y ^ $(lit b))
  | (a, b) => `(bbPoly| x ^ $(lit a) * y ^ $(lit b))

/-- Delaborate `fun g => if g = (a₁, b₁) ∨ … then 1 else 0` back to `poly[…]`.
Fires only on a lambda of exactly that shape, of type
`ZMod ℓ × ZMod m → ZMod 2`, with literal exponents and without a `Classical`
decidability instance (a `classical` indicator would print the same but
re-elaborate to a different term); every other lambda is left to the default
printer. Scoped with the notation. -/
@[scoped delab lam]
def delabPolyLit : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
    let e ← getExpr
    let .lam _ dom body _ := e | failure
    unless body.isAppOfArity ``ite 5 do failure
    let dom ← Meta.whnfR dom
    unless dom.isAppOfArity ``Prod 2 && (dom.getArg! 0).isAppOfArity ``ZMod 1 &&
        (dom.getArg! 1).isAppOfArity ``ZMod 1 do failure
    let cod ← Meta.whnfR (body.getArg! 0)
    unless cod.isAppOfArity ``ZMod 1 && numeral? (cod.getArg! 0) == some 2 do failure
    if ((body.getArg! 2).find? fun c => c.isConstOf ``Classical.propDecidable).isSome then
      failure
    unless numeral? (body.getArg! 3) == some 1 && numeral? (body.getArg! 4) == some 0 do
      failure
    let some mons := exponentPoints? (body.getArg! 1) | failure
    let some first := mons.head? | failure
    let mut p ← monomialSyntax first
    for m in mons.tail do
      p ← `(bbPoly| $p + $(← monomialSyntax m))
    `(poly[$p])

end PolyDelab

end PolyNotation

@[simp] lemma conv_apply (a b : G → ZMod 2) (g : G) :
    (a ⋆ b) g = ∑ h : G, a h * b (g - h) := rfl

/-- Convolution is commutative on an abelian group. -/
lemma conv_comm (a b : G → ZMod 2) : a ⋆ b = b ⋆ a :=
  funext fun g => Fintype.sum_equiv (Equiv.subLeft g) _ _ fun h => by simp [mul_comm]

/-- Convolution with the zero chain on the left vanishes. -/
lemma conv_zero_left (a : G → ZMod 2) : (0 : G → ZMod 2) ⋆ a = 0 := by
  funext g
  simp only [conv_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- Convolution with the zero chain on the right vanishes. -/
lemma conv_zero_right (a : G → ZMod 2) : a ⋆ (0 : G → ZMod 2) = 0 := by
  rw [conv_comm, conv_zero_left]

/-- Convolution is associative. -/
lemma conv_assoc (a b c : G → ZMod 2) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  funext g
  simp only [conv_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  -- reindex the inner sum by `h ↦ h - k`
  exact Finset.sum_congr rfl fun k _ => Fintype.sum_equiv (Equiv.subRight k) _ _ fun h => by
    simp [mul_assoc]

/-- Convolution distributes over addition in the left factor. -/
lemma conv_add_left (a b c : G → ZMod 2) :
    (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  funext g
  simp only [conv_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Convolution distributes over addition in the right factor. -/
lemma conv_add_right (a b c : G → ZMod 2) :
    a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  funext g
  simp only [conv_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Convolution commutes with scalar multiplication in the left factor. -/
lemma conv_smul_left (s : ZMod 2) (a b : G → ZMod 2) :
    (s • a) ⋆ b = s • (a ⋆ b) := by
  funext g
  simp only [conv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Convolution commutes with scalar multiplication in the right factor. -/
lemma conv_smul_right (s : ZMod 2) (a b : G → ZMod 2) :
    a ⋆ (s • b) = s • (a ⋆ b) := by
  rw [conv_comm, conv_smul_left, conv_comm]

/-- `a ⋆ b + b ⋆ a = 0`: convolution is commutative and the coefficients have
characteristic 2. -/
lemma conv_add_swap_eq_zero (a b : G → ZMod 2) :
    a ⋆ b + b ⋆ a = 0 := by
  rw [conv_comm b a]
  exact funext fun g => CharTwo.add_self_eq_zero _

/-- Convolving with a point mass on the left translates: `δ_a ⋆ b = b (· - a)`.
-/
lemma conv_single_left [DecidableEq G] (a : G) (b : G → ZMod 2) :
    Pi.single a 1 ⋆ b = fun g => b (g - a) := by
  funext g
  simp [Pi.single_apply]

/-- Pointwise form of `conv_single_left`. -/
@[simp] lemma conv_single_left_apply [DecidableEq G] (a : G) (b : G → ZMod 2)
    (g : G) :
    (Pi.single a 1 ⋆ b) g = b (g - a) := by
  rw [conv_single_left]

/-- Convolving with a point mass on the right translates:
`(b ⋆ δ_a) g = b (g - a)`. -/
lemma conv_single_right_apply [DecidableEq G] (a : G) (b : G → ZMod 2) (g : G) :
    (b ⋆ Pi.single a 1) g = b (g - a) := by
  rw [conv_comm, conv_single_left]

/-! ## Translation of chains -/

/-- Translation of a chain by a group element: `(translate c v) g = v (g + c)`.
-/
def translate (c : G) (v : G → ZMod 2) : G → ZMod 2 := fun g => v (g + c)

omit [Fintype G] in
@[simp] lemma translate_apply (c : G) (v : G → ZMod 2) (g : G) :
    translate c v g = v (g + c) := rfl

/-- Convolution commutes with translation of the right factor. -/
lemma conv_translate (a v : G → ZMod 2) (c : G) :
    a ⋆ translate c v = translate c (a ⋆ v) := by
  funext g
  simp only [conv_apply, translate_apply, sub_add_eq_add_sub]

/-! ## The boundary maps

The cells are `C₀ = G` (Z-checks), `C₁ = G × Fin 2` (qubits, indexed by a group
element and a block) and `C₂ = G` (X-checks). The boundary maps are

* `∂₂ f = (A ⋆ f | B ⋆ f)`, and
* `∂₁ c = B ⋆ c_L + A ⋆ c_R`, where `c_L = leftHalf c` and `c_R = rightHalf c`.

Each is given first as a plain function (`bbBoundary2Fn`, `bbBoundary1Fn`),
which `decide` can evaluate, and then as a linear map (`bbBoundary2`,
`bbBoundary1`). -/

variable (A B : G → ZMod 2)

/-- The left half of a 1-chain: its restriction to the block `G × {0}`. -/
def leftHalf (c : G × Fin 2 → ZMod 2) : G → ZMod 2 := fun g => c (g, 0)

/-- The right half of a 1-chain: its restriction to the block `G × {1}`. -/
def rightHalf (c : G × Fin 2 → ZMod 2) : G → ZMod 2 := fun g => c (g, 1)

omit [Fintype G] [AddCommGroup G] in
/-- A 1-chain is determined by its two halves. -/
lemma halves_ext_iff {c d : G × Fin 2 → ZMod 2} :
    c = d ↔ leftHalf c = leftHalf d ∧ rightHalf c = rightHalf d := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hL, hR⟩ => funext fun ⟨g, j⟩ => ?_⟩
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  exacts [congrFun hL g, congrFun hR g]

/-- The boundary map `∂₂ f = (A ⋆ f | B ⋆ f)` as a plain function. -/
def bbBoundary2Fn (f : G → ZMod 2) : G × Fin 2 → ZMod 2 :=
  fun ⟨h, j⟩ => if j = 0 then (A ⋆ f) h else (B ⋆ f) h

/-- The boundary map `∂₁ c = B ⋆ c_L + A ⋆ c_R` as a plain function. -/
def bbBoundary1Fn (c : G × Fin 2 → ZMod 2) : G → ZMod 2 :=
  fun g => (B ⋆ leftHalf c) g + (A ⋆ rightHalf c) g

/-- The left half of `∂₂ f` is `A ⋆ f`. -/
lemma leftHalf_bbBoundary2Fn (f : G → ZMod 2) :
    leftHalf (bbBoundary2Fn A B f) = A ⋆ f := rfl

/-- The right half of `∂₂ f` is `B ⋆ f`. -/
lemma rightHalf_bbBoundary2Fn (f : G → ZMod 2) :
    rightHalf (bbBoundary2Fn A B f) = B ⋆ f := rfl

/-- `∂₂ f = 0` iff both `A ⋆ f = 0` and `B ⋆ f = 0`. -/
lemma bbBoundary2Fn_eq_zero_iff (f : G → ZMod 2) :
    bbBoundary2Fn A B f = 0 ↔ A ⋆ f = 0 ∧ B ⋆ f = 0 :=
  halves_ext_iff

/-- `∂₁ c = B ⋆ c_L + A ⋆ c_R` as an equation between chains. -/
lemma bbBoundary1Fn_eq (c : G × Fin 2 → ZMod 2) :
    bbBoundary1Fn A B c = B ⋆ leftHalf c + A ⋆ rightHalf c := rfl

/-- `∂₂` as a `ZMod 2`-linear map. -/
noncomputable def bbBoundary2 :
    (G → ZMod 2) →ₗ[ZMod 2] (G × Fin 2 → ZMod 2) where
  toFun := bbBoundary2Fn A B
  map_add' f₁ f₂ := halves_ext_iff.mpr ⟨conv_add_right A f₁ f₂, conv_add_right B f₁ f₂⟩
  map_smul' s f := halves_ext_iff.mpr ⟨conv_smul_right s A f, conv_smul_right s B f⟩

/-- `∂₁` as a `ZMod 2`-linear map. -/
noncomputable def bbBoundary1 :
    (G × Fin 2 → ZMod 2) →ₗ[ZMod 2] (G → ZMod 2) where
  toFun := bbBoundary1Fn A B
  map_add' c₁ c₂ := by
    change B ⋆ (leftHalf c₁ + leftHalf c₂) + A ⋆ (rightHalf c₁ + rightHalf c₂) = _
    rw [conv_add_right, conv_add_right, add_add_add_comm]
    rfl
  map_smul' s c := by
    change B ⋆ (s • leftHalf c) + A ⋆ (s • rightHalf c) = _
    rw [conv_smul_right, conv_smul_right, ← smul_add]
    rfl

/-- The linear map `∂₂` applies the plain function `bbBoundary2Fn`. -/
@[simp] lemma bbBoundary2_apply (f : G → ZMod 2) :
    bbBoundary2 A B f = bbBoundary2Fn A B f := rfl

/-- The linear map `∂₁` applies the plain function `bbBoundary1Fn`. -/
@[simp] lemma bbBoundary1_apply (c : G × Fin 2 → ZMod 2) :
    bbBoundary1 A B c = bbBoundary1Fn A B c := rfl

/-- `∂₂`, as a plain function, is additive. -/
lemma bbBoundary2Fn_add (f₁ f₂ : G → ZMod 2) :
    bbBoundary2Fn A B (f₁ + f₂) = bbBoundary2Fn A B f₁ + bbBoundary2Fn A B f₂ :=
  map_add (bbBoundary2 A B) f₁ f₂

/-- `∂₁`, as a plain function, is additive. -/
lemma bbBoundary1Fn_add (c₁ c₂ : G × Fin 2 → ZMod 2) :
    bbBoundary1Fn A B (c₁ + c₂) = bbBoundary1Fn A B c₁ + bbBoundary1Fn A B c₂ :=
  map_add (bbBoundary1 A B) c₁ c₂

/-- The chain-complex law for the plain functions: `∂₁ (∂₂ f) = 0`, since
`B ⋆ (A ⋆ f) + A ⋆ (B ⋆ f) = (B ⋆ A + A ⋆ B) ⋆ f = 0`. -/
lemma bbBoundaryFn_comp (f : G → ZMod 2) :
    bbBoundary1Fn A B (bbBoundary2Fn A B f) = 0 := by
  rw [bbBoundary1Fn_eq, leftHalf_bbBoundary2Fn, rightHalf_bbBoundary2Fn, ← conv_assoc,
    ← conv_assoc, ← conv_add_left, conv_add_swap_eq_zero, conv_zero_left]

/-- The chain-complex law `∂₁ ∘ ∂₂ = 0`. -/
lemma bbBoundary_comp : (bbBoundary1 A B).comp (bbBoundary2 A B) = 0 :=
  LinearMap.ext (bbBoundaryFn_comp A B)

/-! ## Translation equivariance of the boundary maps -/

/-- Translation of a 1-chain by a group element, acting on each block. -/
def translate1 (c : G) (v : G × Fin 2 → ZMod 2) : G × Fin 2 → ZMod 2 :=
  fun p => v (p.1 + c, p.2)

omit [Fintype G] in
@[simp] lemma translate1_apply (c : G) (v : G × Fin 2 → ZMod 2)
    (p : G × Fin 2) :
    translate1 c v p = v (p.1 + c, p.2) := rfl

omit [Fintype G] in
/-- Translating a 1-chain translates its left half. -/
lemma leftHalf_translate1 (c : G) (v : G × Fin 2 → ZMod 2) :
    leftHalf (translate1 c v) = translate c (leftHalf v) := rfl

omit [Fintype G] in
/-- Translating a 1-chain translates its right half. -/
lemma rightHalf_translate1 (c : G) (v : G × Fin 2 → ZMod 2) :
    rightHalf (translate1 c v) = translate c (rightHalf v) := rfl

/-- `∂₁` is translation-equivariant. -/
lemma bbBoundary1Fn_translate1 (c : G) (v : G × Fin 2 → ZMod 2) :
    bbBoundary1Fn A B (translate1 c v) = translate c (bbBoundary1Fn A B v) := by
  rw [bbBoundary1Fn_eq, leftHalf_translate1, rightHalf_translate1, conv_translate,
    conv_translate]
  rfl

/-- `∂₂` is translation-equivariant. -/
lemma bbBoundary2Fn_translate (c : G) (f : G → ZMod 2) :
    bbBoundary2Fn A B (translate c f) = translate1 c (bbBoundary2Fn A B f) :=
  halves_ext_iff.mpr ⟨conv_translate A f c, conv_translate B f c⟩

/-! ## Packaging as a `HomologicalCode` -/

/-- The number of qubits of a bivariate bicycle code over `G`: `2 * |G|`. -/
def bbNumQubits (G : Type) [Fintype G] : ℕ := 2 * Fintype.card G

/-- A numbering of the 1-cells `G × Fin 2` by `Fin (bbNumQubits G)`. -/
noncomputable def bbEdgeEquiv : G × Fin 2 ≃ Fin (bbNumQubits G) :=
  (((Fintype.equivFin G).prodCongr (Equiv.refl (Fin 2))).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_comm _ 2))

omit [AddCommGroup G] in
/-- There are `bbNumQubits G` 1-cells. -/
lemma bbCard_C1 : Fintype.card (G × Fin 2) = bbNumQubits G := by
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm, bbNumQubits]

variable [DecidableEq G]

/-- The bivariate bicycle chain complex of `A`, `B` as a `HomologicalCode`:
cells `C₀ = C₂ = G` and `C₁ = G × Fin 2`, with the boundary maps `bbBoundary1`
and `bbBoundary2`. -/
noncomputable def bbChainComplex (A B : G → ZMod 2) : HomologicalCode where
  C0 := G
  C1 := G × Fin 2
  C2 := G
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := bbBoundary1 A B
  boundary2 := bbBoundary2 A B
  boundary_comp := bbBoundary_comp A B
  numQubits := bbNumQubits G
  numQubits_eq := bbCard_C1
  edgeEquiv := bbEdgeEquiv

/-! ## Round-trip tests

`poly[…]` expands to exactly the indicator-function normal form, and `⋆` to
`conv`. -/

section RoundTrip

example :
    (poly[x^3 + y + y^2] : ZMod 12 × ZMod 6 → ZMod 2) =
      fun g => if g = (3, 0) ∨ g = (0, 1) ∨ g = (0, 2) then 1 else 0 :=
  rfl

example :
    (poly[y^3 + x + x^2] : ZMod 12 × ZMod 6 → ZMod 2) =
      fun g => if g = (0, 3) ∨ g = (1, 0) ∨ g = (2, 0) then 1 else 0 :=
  rfl

example :
    (poly[1 + x^2] : ZMod 12 × ZMod 6 → ZMod 2) =
      fun g => if g = (0, 0) ∨ g = (2, 0) then 1 else 0 :=
  rfl

example : (poly[x^6] : ZMod 12 × ZMod 6 → ZMod 2) = fun g => if g = (6, 0) then 1 else 0 :=
  rfl

example :
    (poly[x*y^2 + x^2*y + x*y] : ZMod 3 × ZMod 3 → ZMod 2) =
      fun g => if g = (1, 2) ∨ g = (2, 1) ∨ g = (1, 1) then 1 else 0 :=
  rfl

example (a b : G → ZMod 2) : a ⋆ b = conv a b := rfl

example (a b c : G → ZMod 2) : a ⋆ b ⋆ c = conv (conv a b) c := rfl

example (a b : G → ZMod 2) (g : G) : (a ⋆ b) g = conv a b g := rfl

open Lean Elab Command in
/-- Display test: elaborate `stx` and check that its pretty-printed text is
`expected` (`exact := false`: contains `expected`). Run through `run_cmd` so no
`#`-command is needed. -/
private def checkDisplay (stx : Syntax) (expected : String) (exact : Bool := true) :
    CommandElabM Unit :=
  liftTermElabM do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let s := toString (← Meta.ppExpr (← instantiateMVars e))
    unless (if exact then s == expected else (s.splitOn expected).length > 1) do
      throwError "display test failed:{indentD s}\nexpected{indentD expected}"

run_cmd do
  checkDisplay (← `((poly[x^3 + y + y^2] : ZMod 12 × ZMod 6 → ZMod 2)))
    "poly[x^3 + y + y^2]"
run_cmd do
  checkDisplay (← `((poly[1 + x*y^2] : ZMod 3 × ZMod 3 → ZMod 2))) "poly[1 + x*y^2]"
-- an indicator of the same shape over another type is not a bivariate-bicycle polynomial
run_cmd do
  checkDisplay (← `(fun p : ℕ × ℕ => if p = (1, 2) ∨ p = (0, 3) then (1 : ℕ) else 0))
    "if p = (1, 2) ∨ p = (0, 3) then 1 else 0" (exact := false)
run_cmd do
  checkDisplay (← `(fun (a b : ZMod 12 × ZMod 6 → ZMod 2) => a ⋆ b))
    "a ⋆ b" (exact := false)

end RoundTrip

end BB
end Homological
end Stabilizer
end Quantum
