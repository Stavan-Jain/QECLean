import Mathlib.Tactic

/-!
# Cells of the rotated surface code

The rotated surface code of odd size `L ≥ 3` has one qubit on every site of an
`L × L` grid and one check on every cell of a checkerboard colouring of the
grid, completed by weight-two checks along the four edges. This file defines
the index types of the qubits and of the checks, and the set of qubits each
check acts on.

## Lattice conventions

* Qubits are the sites `(x, y) : VtxIdx L = Fin L × Fin L`, where `x` is the
  column (`0` is leftmost) and `y` is the row (`0` is topmost). The qubit
  `(x, y)` has number `y * L + x`.
* An interior cell is the 2×2 block of sites with top-left site
  `(x, y) : FaceCornerIdx L`, covering `(x, y)`, `(x+1, y)`, `(x, y+1)` and
  `(x+1, y+1)` (`faceQubits`). It carries a Z-check if `x + y` is even
  (`ZInteriorCornerIdx`) and an X-check if `x + y` is odd
  (`XInteriorCornerIdx`).
* The left and right edges carry weight-two Z-checks and the top and bottom
  edges weight-two X-checks, `(L - 1) / 2` on each edge (`RscBdyIdx`):
  `leftBdy k` acts on `(0, 2k+1)`, `(0, 2k+2)`, `rightBdy k` on `(L-1, 2k)`,
  `(L-1, 2k+1)`, `topBdy k` on `(2k, 0)`, `(2k+1, 0)`, and `bottomBdy k` on
  `(2k+1, L-1)`, `(2k+2, L-1)`.

## Main definitions and results

* `ZFaceIdx L`, `XFaceIdx L`: the Z-checks and the X-checks.
* `zFaceSupport`, `xFaceSupport`: the qubits a check acts on, with the
  membership lemmas `mem_zFaceSupport_interior_iff`, …,
  `mem_xFaceSupport_bottomBdy_iff`.
* `block L (a, b)`: the sites `(x, y)` of the grid with `x ∈ {a - 1, a}` and
  `y ∈ {b - 1, b}`. Every check, interior or not, acts on the block of its
  bottom-right site `zFaceCorner` or `xFaceCorner` (`zFaceSupport_eq_block`,
  `xFaceSupport_eq_block`), which may lie one step outside the grid; `a + b`
  is even for a Z-check and odd for an X-check.
* `even_card_zFaceSupport_inter_xFaceSupport`: a Z-check and an X-check share
  an even number of qubits.
* `even_card_row_inter_xFaceSupport`, `even_card_col_inter_zFaceSupport`: an
  X-check meets every row, and a Z-check every column, in an even number of
  qubits.
* `card_ZFaceIdx_add_card_XFaceIdx`: there are `L * L - 1` checks.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice
namespace RotatedSurface

/-! ## Index types -/

/-- Data qubits of the `L × L` rotated surface code, indexed `(x, y)` with `x`
the column (`0` leftmost) and `y` the row (`0` topmost). -/
abbrev VtxIdx (L : ℕ) : Type := Fin L × Fin L

/-- Top-left sites of the interior cells. The cell at `(x, y)` covers the
qubits `(x, y)`, `(x+1, y)`, `(x, y+1)` and `(x+1, y+1)`. -/
abbrev FaceCornerIdx (L : ℕ) : Type := Fin (L - 1) × Fin (L - 1)

/-- Interior cells carrying a Z-check: those with `x + y` even. -/
def ZInteriorCornerIdx (L : ℕ) : Type :=
  { c : FaceCornerIdx L // (c.1.val + c.2.val) % 2 = 0 }

/-- Interior cells carrying an X-check: those with `x + y` odd. -/
def XInteriorCornerIdx (L : ℕ) : Type :=
  { c : FaceCornerIdx L // (c.1.val + c.2.val) % 2 = 1 }

instance (L : ℕ) : DecidableEq (ZInteriorCornerIdx L) := Subtype.instDecidableEq
instance (L : ℕ) : DecidableEq (XInteriorCornerIdx L) := Subtype.instDecidableEq
instance (L : ℕ) : Fintype (ZInteriorCornerIdx L) := Subtype.fintype _
instance (L : ℕ) : Fintype (XInteriorCornerIdx L) := Subtype.fintype _

/-- Index of a weight-two check along one edge of the grid; there are
`(L - 1) / 2` of them on each edge. -/
abbrev RscBdyIdx (L : ℕ) : Type := Fin ((L - 1) / 2)

/-- The Z-checks: the interior cells with `x + y` even, and the weight-two
checks `leftBdy k` on `(0, 2k+1)`, `(0, 2k+2)` and `rightBdy k` on
`(L-1, 2k)`, `(L-1, 2k+1)`. -/
inductive ZFaceIdx (L : ℕ)
  | interior (c : ZInteriorCornerIdx L) : ZFaceIdx L
  | leftBdy (k : RscBdyIdx L) : ZFaceIdx L
  | rightBdy (k : RscBdyIdx L) : ZFaceIdx L
  deriving DecidableEq

/-- The X-checks: the interior cells with `x + y` odd, and the weight-two
checks `topBdy k` on `(2k, 0)`, `(2k+1, 0)` and `bottomBdy k` on
`(2k+1, L-1)`, `(2k+2, L-1)`. -/
inductive XFaceIdx (L : ℕ)
  | interior (c : XInteriorCornerIdx L) : XFaceIdx L
  | topBdy (k : RscBdyIdx L) : XFaceIdx L
  | bottomBdy (k : RscBdyIdx L) : XFaceIdx L
  deriving DecidableEq

/-- The Z-checks as a sum of their three kinds. -/
def zFaceIdxEquivSum (L : ℕ) :
    ZFaceIdx L ≃ (ZInteriorCornerIdx L ⊕ RscBdyIdx L ⊕ RscBdyIdx L) where
  toFun
    | .interior c => Sum.inl c
    | .leftBdy k => Sum.inr (Sum.inl k)
    | .rightBdy k => Sum.inr (Sum.inr k)
  invFun
    | Sum.inl c => .interior c
    | Sum.inr (Sum.inl k) => .leftBdy k
    | Sum.inr (Sum.inr k) => .rightBdy k
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

/-- The X-checks as a sum of their three kinds. -/
def xFaceIdxEquivSum (L : ℕ) :
    XFaceIdx L ≃ (XInteriorCornerIdx L ⊕ RscBdyIdx L ⊕ RscBdyIdx L) where
  toFun
    | .interior c => Sum.inl c
    | .topBdy k => Sum.inr (Sum.inl k)
    | .bottomBdy k => Sum.inr (Sum.inr k)
  invFun
    | Sum.inl c => .interior c
    | Sum.inr (Sum.inl k) => .topBdy k
    | Sum.inr (Sum.inr k) => .bottomBdy k
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

instance (L : ℕ) : Fintype (ZFaceIdx L) :=
  Fintype.ofEquiv _ (zFaceIdxEquivSum L).symm

instance (L : ℕ) : Fintype (XFaceIdx L) :=
  Fintype.ofEquiv _ (xFaceIdxEquivSum L).symm

/-! ## Supports of the checks -/

/-- The index `i : Fin (L - 1)` as an index in `Fin L`. -/
@[inline] def cornerLo {L : ℕ} (i : Fin (L - 1)) : Fin L :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- The index `i + 1` in `Fin L`, for `i : Fin (L - 1)`. -/
@[inline] def cornerHi {L : ℕ} (i : Fin (L - 1)) : Fin L :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

/-- The four qubits of the interior cell with top-left site `c`. -/
def faceQubits {L : ℕ} (c : FaceCornerIdx L) : Finset (VtxIdx L) :=
  {(cornerLo c.1, cornerLo c.2),
   (cornerHi c.1, cornerLo c.2),
   (cornerLo c.1, cornerHi c.2),
   (cornerHi c.1, cornerHi c.2)}

/-- The qubits the Z-check `zf` acts on. -/
def zFaceSupport {L : ℕ} : ZFaceIdx L → Finset (VtxIdx L)
  | .interior c => faceQubits c.val
  | .leftBdy k =>
      let x0 : Fin L := ⟨0, by have := k.isLt; omega⟩
      let y1 : Fin L := ⟨2 * k.val + 1, by have := k.isLt; omega⟩
      let y2 : Fin L := ⟨2 * k.val + 2, by have := k.isLt; omega⟩
      {(x0, y1), (x0, y2)}
  | .rightBdy k =>
      let xR : Fin L := ⟨L - 1, by have := k.isLt; omega⟩
      let y0 : Fin L := ⟨2 * k.val, by have := k.isLt; omega⟩
      let y1 : Fin L := ⟨2 * k.val + 1, by have := k.isLt; omega⟩
      {(xR, y0), (xR, y1)}

/-- The qubits the X-check `xf` acts on. -/
def xFaceSupport {L : ℕ} : XFaceIdx L → Finset (VtxIdx L)
  | .interior c => faceQubits c.val
  | .topBdy k =>
      let y0 : Fin L := ⟨0, by have := k.isLt; omega⟩
      let x0 : Fin L := ⟨2 * k.val, by have := k.isLt; omega⟩
      let x1 : Fin L := ⟨2 * k.val + 1, by have := k.isLt; omega⟩
      {(x0, y0), (x1, y0)}
  | .bottomBdy k =>
      let yB : Fin L := ⟨L - 1, by have := k.isLt; omega⟩
      let x1 : Fin L := ⟨2 * k.val + 1, by have := k.isLt; omega⟩
      let x2 : Fin L := ⟨2 * k.val + 2, by have := k.isLt; omega⟩
      {(x1, yB), (x2, yB)}

variable {L : ℕ}

lemma zFaceSupport_interior (c : ZInteriorCornerIdx L) :
    zFaceSupport (.interior c) = faceQubits c.val := rfl

lemma xFaceSupport_interior (c : XInteriorCornerIdx L) :
    xFaceSupport (.interior c) = faceQubits c.val := rfl

/-- A qubit lies in the cell with top-left site `c` iff its column is `c.1` or
`c.1 + 1` and its row is `c.2` or `c.2 + 1`. -/
lemma mem_faceQubits_iff (c : FaceCornerIdx L) (v : VtxIdx L) :
    v ∈ faceQubits c ↔
      (v.1.val = c.1.val ∨ v.1.val = c.1.val + 1) ∧
      (v.2.val = c.2.val ∨ v.2.val = c.2.val + 1) := by
  simp only [faceQubits, cornerLo, cornerHi, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff, Fin.ext_iff]
  tauto

lemma mem_zFaceSupport_interior_iff (c : ZInteriorCornerIdx L) (v : VtxIdx L) :
    v ∈ zFaceSupport (.interior c) ↔
      (v.1.val = c.val.1.val ∨ v.1.val = c.val.1.val + 1) ∧
      (v.2.val = c.val.2.val ∨ v.2.val = c.val.2.val + 1) :=
  mem_faceQubits_iff _ _

lemma mem_xFaceSupport_interior_iff (c : XInteriorCornerIdx L) (v : VtxIdx L) :
    v ∈ xFaceSupport (.interior c) ↔
      (v.1.val = c.val.1.val ∨ v.1.val = c.val.1.val + 1) ∧
      (v.2.val = c.val.2.val ∨ v.2.val = c.val.2.val + 1) :=
  mem_faceQubits_iff _ _

lemma mem_zFaceSupport_leftBdy_iff (k : RscBdyIdx L) (v : VtxIdx L) :
    v ∈ zFaceSupport (.leftBdy k) ↔
      v.1.val = 0 ∧ (v.2.val = 2 * k.val + 1 ∨ v.2.val = 2 * k.val + 2) := by
  simp only [zFaceSupport, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff]
  tauto

lemma mem_zFaceSupport_rightBdy_iff (k : RscBdyIdx L) (v : VtxIdx L) :
    v ∈ zFaceSupport (.rightBdy k) ↔
      v.1.val = L - 1 ∧ (v.2.val = 2 * k.val ∨ v.2.val = 2 * k.val + 1) := by
  simp only [zFaceSupport, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff]
  tauto

lemma mem_xFaceSupport_topBdy_iff (k : RscBdyIdx L) (v : VtxIdx L) :
    v ∈ xFaceSupport (.topBdy k) ↔
      v.2.val = 0 ∧ (v.1.val = 2 * k.val ∨ v.1.val = 2 * k.val + 1) := by
  simp only [xFaceSupport, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff]
  tauto

lemma mem_xFaceSupport_bottomBdy_iff (k : RscBdyIdx L) (v : VtxIdx L) :
    v ∈ xFaceSupport (.bottomBdy k) ↔
      v.2.val = L - 1 ∧ (v.1.val = 2 * k.val + 1 ∨ v.1.val = 2 * k.val + 2) := by
  simp only [xFaceSupport, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff]
  tauto

/-! ## Checks as blocks

Every check acts on the part inside the grid of a 2×2 block of sites. The
block is named by its bottom-right site `(a, b)`, with `0 ≤ a, b ≤ L`: the
weight-two checks are the blocks that stick out of the grid by one column
(`a = 0` or `a = L`) or by one row (`b = 0` or `b = L`). -/

/-- The coordinates `a - 1` and `a` that lie in `Fin L`. -/
def strip (L a : ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun x => x.val + 1 = a ∨ x.val = a

/-- The sites `(x, y)` of the `L × L` grid with `x ∈ {a - 1, a}` and
`y ∈ {b - 1, b}`, where `p = (a, b)`. -/
def block (L : ℕ) (p : ℕ × ℕ) : Finset (VtxIdx L) :=
  strip L p.1 ×ˢ strip L p.2

@[simp] lemma mem_strip {a : ℕ} {x : Fin L} :
    x ∈ strip L a ↔ x.val + 1 = a ∨ x.val = a := by
  simp [strip]

@[simp] lemma mem_block {p : ℕ × ℕ} {v : VtxIdx L} :
    v ∈ block L p ↔
      (v.1.val + 1 = p.1 ∨ v.1.val = p.1) ∧ (v.2.val + 1 = p.2 ∨ v.2.val = p.2) := by
  simp [block]

/-- A strip inside the grid has two elements. -/
lemma card_strip {a : ℕ} (h0 : 0 < a) (hL : a < L) : (strip L a).card = 2 := by
  have h : strip L a = {⟨a - 1, by omega⟩, ⟨a, hL⟩} := by
    ext x
    simp only [mem_strip, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [h, Finset.card_pair (by simp only [ne_eq, Fin.mk.injEq]; omega)]

/-- Strips two or more steps apart are disjoint. -/
lemma strip_inter_strip_eq_empty {a a' : ℕ} (h : a + 2 ≤ a' ∨ a' + 2 ≤ a) :
    strip L a ∩ strip L a' = ∅ := by
  ext x
  simp only [Finset.mem_inter, mem_strip, Finset.notMem_empty, iff_false]
  omega

/-- Two blocks `p` and `q` of opposite colour (`p.1 + p.2` and `q.1 + q.2` of
different parity) share an even number of sites, provided the rows of `p` and
the columns of `q` lie inside the grid: the blocks are disjoint or share a
whole row or a whole column of two sites. -/
theorem even_card_block_inter_block {p q : ℕ × ℕ}
    (hpar : (p.1 + p.2 + q.1 + q.2) % 2 = 1)
    (hp : 0 < p.2 ∧ p.2 < L) (hq : 0 < q.1 ∧ q.1 < L) :
    Even (block L p ∩ block L q).card := by
  rw [block, block, Finset.product_inter_product, Finset.card_product]
  by_cases h1 : p.1 = q.1
  · rw [h1, Finset.inter_self, card_strip hq.1 hq.2]
    exact even_two.mul_right _
  by_cases h2 : p.2 = q.2
  · rw [← h2, Finset.inter_self, card_strip hp.1 hp.2]
    exact even_two.mul_left _
  obtain h | h : (p.1 + 2 ≤ q.1 ∨ q.1 + 2 ≤ p.1) ∨ (p.2 + 2 ≤ q.2 ∨ q.2 + 2 ≤ p.2) := by omega
  · simp [strip_inter_strip_eq_empty h]
  · simp [strip_inter_strip_eq_empty h]

/-- A block whose columns lie inside the grid meets every row of the grid in
an even number of sites: none, or the two sites of the row in those columns. -/
lemma even_card_row_inter_block {p : ℕ × ℕ} (hp : 0 < p.1 ∧ p.1 < L) (y : Fin L) :
    Even ((Finset.univ.filter fun v : VtxIdx L => v.2 = y) ∩ block L p).card := by
  have h : (Finset.univ.filter fun v : VtxIdx L => v.2 = y) = Finset.univ ×ˢ {y} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
  rw [h, block, Finset.product_inter_product, Finset.card_product, Finset.univ_inter,
    card_strip hp.1 hp.2]
  exact even_two.mul_right _

/-- A block whose rows lie inside the grid meets every column of the grid in
an even number of sites: none, or the two sites of the column in those rows. -/
lemma even_card_col_inter_block {p : ℕ × ℕ} (hp : 0 < p.2 ∧ p.2 < L) (x : Fin L) :
    Even ((Finset.univ.filter fun v : VtxIdx L => v.1 = x) ∩ block L p).card := by
  have h : (Finset.univ.filter fun v : VtxIdx L => v.1 = x) = {x} ×ˢ Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_product,
      Finset.mem_singleton]
  rw [h, block, Finset.product_inter_product, Finset.card_product, Finset.univ_inter,
    card_strip hp.1 hp.2]
  exact even_two.mul_left _

/-- The bottom-right site of the block of a Z-check. -/
def zFaceCorner : ZFaceIdx L → ℕ × ℕ
  | .interior c => (c.val.1.val + 1, c.val.2.val + 1)
  | .leftBdy k => (0, 2 * k.val + 2)
  | .rightBdy k => (L, 2 * k.val + 1)

/-- The bottom-right site of the block of an X-check. -/
def xFaceCorner : XFaceIdx L → ℕ × ℕ
  | .interior c => (c.val.1.val + 1, c.val.2.val + 1)
  | .topBdy k => (2 * k.val + 1, 0)
  | .bottomBdy k => (2 * k.val + 2, L)

/-- A Z-check acts on the block of its corner. -/
lemma zFaceSupport_eq_block (zf : ZFaceIdx L) :
    zFaceSupport zf = block L (zFaceCorner zf) := by
  ext v
  rcases zf with c | k | k
  · rw [mem_zFaceSupport_interior_iff, mem_block]
    simp only [zFaceCorner, add_left_inj]
  · rw [mem_zFaceSupport_leftBdy_iff, mem_block]
    simp only [zFaceCorner]
    omega
  · rw [mem_zFaceSupport_rightBdy_iff, mem_block]
    simp only [zFaceCorner]
    omega

/-- An X-check acts on the block of its corner. -/
lemma xFaceSupport_eq_block (xf : XFaceIdx L) :
    xFaceSupport xf = block L (xFaceCorner xf) := by
  ext v
  rcases xf with c | k | k
  · rw [mem_xFaceSupport_interior_iff, mem_block]
    simp only [xFaceCorner, add_left_inj]
  · rw [mem_xFaceSupport_topBdy_iff, mem_block]
    simp only [xFaceCorner]
    omega
  · rw [mem_xFaceSupport_bottomBdy_iff, mem_block]
    simp only [xFaceCorner]
    omega

/-- The block of a Z-check sticks out of the grid by at most one column, and
its rows lie inside the grid. -/
lemma zFaceCorner_bounds (zf : ZFaceIdx L) :
    (zFaceCorner zf).1 ≤ L ∧ 0 < (zFaceCorner zf).2 ∧ (zFaceCorner zf).2 < L := by
  rcases zf with c | k | k <;> simp only [zFaceCorner] <;> omega

/-- The block of an X-check sticks out of the grid by at most one row, and its
columns lie inside the grid. -/
lemma xFaceCorner_bounds (xf : XFaceIdx L) :
    0 < (xFaceCorner xf).1 ∧ (xFaceCorner xf).1 < L ∧ (xFaceCorner xf).2 ≤ L := by
  rcases xf with c | k | k <;> simp only [xFaceCorner] <;> omega

/-- The corner `(a, b)` of a Z-check has `a + b` even. -/
lemma zFaceCorner_parity [Fact (Odd L)] (zf : ZFaceIdx L) :
    ((zFaceCorner zf).1 + (zFaceCorner zf).2) % 2 = 0 := by
  have hL : L % 2 = 1 := Nat.odd_iff.mp Fact.out
  rcases zf with c | k | k <;> simp only [zFaceCorner]
  · have := c.2
    omega
  · omega
  · omega

/-- The corner `(a, b)` of an X-check has `a + b` odd. -/
lemma xFaceCorner_parity [Fact (Odd L)] (xf : XFaceIdx L) :
    ((xFaceCorner xf).1 + (xFaceCorner xf).2) % 2 = 1 := by
  have hL : L % 2 = 1 := Nat.odd_iff.mp Fact.out
  rcases xf with c | k | k <;> simp only [xFaceCorner]
  · have := c.2
    omega
  · omega
  · omega

/-- Distinct Z-checks have distinct corners. -/
lemma zFaceCorner_injective : Function.Injective (zFaceCorner (L := L)) := by
  rintro (c | k | k) (c' | k' | k') h <;>
    simp only [zFaceCorner, Prod.mk.injEq] at h <;>
    first
      | omega
      | exact congrArg _ (Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))))
      | exact congrArg _ (Fin.ext (by omega))

/-- Distinct X-checks have distinct corners. -/
lemma xFaceCorner_injective : Function.Injective (xFaceCorner (L := L)) := by
  rintro (c | k | k) (c' | k' | k') h <;>
    simp only [xFaceCorner, Prod.mk.injEq] at h <;>
    first
      | omega
      | exact congrArg _ (Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))))
      | exact congrArg _ (Fin.ext (by omega))

/-- A Z-check and an X-check share an even number of qubits. -/
theorem even_card_zFaceSupport_inter_xFaceSupport [Fact (Odd L)]
    (zf : ZFaceIdx L) (xf : XFaceIdx L) :
    Even (zFaceSupport zf ∩ xFaceSupport xf).card := by
  have hz := zFaceCorner_bounds zf
  have hx := xFaceCorner_bounds xf
  have hzp := zFaceCorner_parity zf
  have hxp := xFaceCorner_parity xf
  rw [zFaceSupport_eq_block, xFaceSupport_eq_block]
  exact even_card_block_inter_block (by omega) hz.2 ⟨hx.1, hx.2.1⟩

/-- An X-check meets every row of the grid in an even number of qubits. -/
theorem even_card_row_inter_xFaceSupport (xf : XFaceIdx L) (y : Fin L) :
    Even ((Finset.univ.filter fun v : VtxIdx L => v.2 = y) ∩ xFaceSupport xf).card := by
  rw [xFaceSupport_eq_block]
  exact even_card_row_inter_block ⟨(xFaceCorner_bounds xf).1, (xFaceCorner_bounds xf).2.1⟩ y

/-- A Z-check meets every column of the grid in an even number of qubits. -/
theorem even_card_col_inter_zFaceSupport (zf : ZFaceIdx L) (x : Fin L) :
    Even ((Finset.univ.filter fun v : VtxIdx L => v.1 = x) ∩ zFaceSupport zf).card := by
  rw [zFaceSupport_eq_block]
  exact even_card_col_inter_block (zFaceCorner_bounds zf).2 x

/-! ## Counting the checks -/

/-- The interior cells are split between Z-checks and X-checks. -/
lemma card_ZInteriorCornerIdx_add_card_XInteriorCornerIdx :
    Fintype.card (ZInteriorCornerIdx L) + Fintype.card (XInteriorCornerIdx L) =
      (L - 1) ^ 2 := by
  have h : ∀ c : FaceCornerIdx L,
      (c.1.val + c.2.val) % 2 = 1 ↔ ¬(c.1.val + c.2.val) % 2 = 0 := fun c => by omega
  simp only [ZInteriorCornerIdx, XInteriorCornerIdx, Fintype.card_subtype, h]
  rw [Finset.card_filter_add_card_filter_not]
  simp [sq]

/-- For odd `L` there are `L * L - 1` checks in total. -/
theorem card_ZFaceIdx_add_card_XFaceIdx [Fact (Odd L)] :
    Fintype.card (ZFaceIdx L) + Fintype.card (XFaceIdx L) = L * L - 1 := by
  obtain ⟨m, rfl⟩ := (Fact.out : Odd L)
  have h := card_ZInteriorCornerIdx_add_card_XInteriorCornerIdx (L := 2 * m + 1)
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [Fintype.card_congr (zFaceIdxEquivSum _), Fintype.card_congr (xFaceIdxEquivSum _)]
  simp only [Fintype.card_sum, Fintype.card_fin, hm]
  rw [Nat.add_sub_cancel] at h
  have e : (2 * m + 1) * (2 * m + 1) = (2 * m) ^ 2 + 4 * m + 1 := by ring
  omega

end RotatedSurface
end Lattice
end Stabilizer
end Quantum
