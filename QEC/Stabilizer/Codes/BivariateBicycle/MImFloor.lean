/-
# Phase 6: the safe-sector confined floor — the native-decidable engine

`MImClassify` reduced the safe-sector weight to `costFromComps` of the ten coset
components `seam offset ⊕ engine-multiplied free datum` (§6, §7).  This module builds
the **finite engine** that decides the floor `≥ 12` over the (2³⁰) coset product, and the
**soundness layer** that turns the engine's `floorOK = true` into the real weight bound.

The engine has three cost layers, all keyed on a ring element's four `Z₂²`-slot values
(`F₄ = 0..3`, `allS` order `(0,0),(1,0),(0,1),(1,1)`; F₄ add `= gadd =` bitwise xor):

* `exCost` — the exact per-coset weight (`wt5N` summed over the eight `(side,slot)` cells);
* `slabMin` — the slab-min lower bound (`cellMin`: min over comps-1,2 support; comps 0,3,4
  exact), which certifies ~97 % of the 16384 `(comp 0,3,4)` slabs in 32 lookups;
* `relaxed` — the offset-aware relaxed lower bound (`rcell`: comps 1,2 by support class,
  with the comp-1,2 **seam offsets baked in**), which certifies ~99 % of the live slabs'
  support classes, leaving only the genuine fibers for the exact `exCost` check.

The **soundness keystones** (`cellMin_le`, `rcell_le`) finite-check that `slabMin`/`relaxed`
really lower-bound `exCost`; the per-cell bridges (`cell_slab_sound`, `cell_relaxed_sound'`)
lift them to coset values, and the **monotone lemmas** (`slabMin_le_exCost`,
`relaxed_le_exCost`) sum the eight cells.  Together they give: `floorOK oL oR = true`
(decided per-orbit in `MImFloorO0`..`MImFloorO4`) ⟹ every coset weight `≥ 12`.

Note (a real soundness subtlety): the raw-support `d3` relaxation is **not** a valid lower
bound, because the comp-1 seam offset is nonzero and shifts supports; `rcell` corrects this
by baking the offsets `(o1,o2)` into the per-cell min.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.MImClassify
import QEC.Stabilizer.Codes.BivariateBicycle.MImFloorData

open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

/-! ## §8 The Nat-encoded cost primitives and the soundness keystones -/

/-- F₄ add on the Nat encoding `0..3` (= bitwise xor = `fadd` on `.val`). -/
@[inline] def gadd (a b : Nat) : Nat := a ^^^ b

/-- `wt5OfComps` on Nat indices (`WT5_TABLE` reused, so `wt5N (·.val) = wt5OfComps`). -/
@[inline] def wt5N (v0 v1 v2 v3 v4 : Nat) : Nat :=
  WT5_TABLE.getD (v0 + 2 * (v1 + 4 * (v2 + 4 * (v3 + 4 * v4)))) 99

/-- The relaxed per-cell d₃ table lookup (`D3V`, comps 0,3,4 exact, comps 1,2 by `(a1,a2)`). -/
@[inline] def d3 (v0 v3 v4 a1 a2 : Nat) : Nat := D3V.getD ((v0*16+v3*4+v4)*4+a1+2*a2) 99

/-- Per-cell slab-min: the min d₃ over the two support bits (comps 1,2 free). -/
@[inline] def cellMin (v0 v3 v4 : Nat) : Nat :=
  min (min (d3 v0 v3 v4 0 0) (d3 v0 v3 v4 1 0)) (min (d3 v0 v3 v4 0 1) (d3 v0 v3 v4 1 1))

/-- Support bit of a Nat value. -/
@[inline] def supp (v : Nat) : Nat := if v == 0 then 0 else 1

/-- The offset-aware relaxed per-cell lookup (`RCELL`): comps 1,2 by support `(b1,b2)` with
their seam offsets `(o1,o2)` baked in. -/
@[inline] def rcell (v0 v3 v4 o1 o2 b1 b2 : Nat) : Nat :=
  RCELL.getD (((((v0*4+v3)*4+v4)*4+o1)*4+o2)*4+b1*2+b2) 99

/-- **Slab-min soundness keystone**: the per-cell slab-min lower-bounds the exact layer
weight for every choice of the comp-1,2 values.  (Finite check over the 512 value-tuples;
`v0 ∈ Fin 2` since comp 0 is the trivial-character, `F₂`-valued component.) -/
theorem cellMin_le : ∀ (v0 : Fin 2) (v1 v2 v3 v4 : Fin 4),
    cellMin v0.val v3.val v4.val ≤ wt5N v0.val v1.val v2.val v3.val v4.val := by
  native_decide

/-- **Relaxed soundness keystone**: the offset-aware relaxed cost lower-bounds the exact
layer weight `wt5N`, for every comp-1,2 offset `(o1,o2)` and entry `(q1,q2)` whose raw
supports key the table.  (`native_decide` over the `2·4⁶` value-tuples.) -/
theorem rcell_le : ∀ (v0 : Fin 2) (v3 v4 o1 o2 q1 q2 : Fin 4),
    rcell v0.val v3.val v4.val o1.val o2.val (supp q1.val) (supp q2.val)
      ≤ wt5N v0.val (gadd o1.val q1.val) (gadd o2.val q2.val) v3.val v4.val := by
  native_decide

/-! ## §9 The per-cell soundness bridges (keystone applied to coset values)

The coset's per-cell component values are `gadd (seam offset) (Γ-pair value)`.  These
lemmas lift the keystones (§8) to those values, discharging the F₄ bounds: `gadd = xor`
keeps `< 2` (comp 0, the `F₂`-valued trivial character) and `< 4` (comps 1–4). -/

theorem gadd_lt_two {a b : Nat} (ha : a < 2) (hb : b < 2) : gadd a b < 2 := by
  interval_cases a <;> interval_cases b <;> decide

theorem gadd_lt_four {a b : Nat} (ha : a < 4) (hb : b < 4) : gadd a b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

/-- Per-cell **slab-min** soundness on actual coset values `gadd offset pair`. -/
theorem cell_slab_sound {o0 q0 o1 q1 o2 q2 o3 q3 o4 q4 : Nat}
    (h0o : o0 < 2) (h0q : q0 < 2) (h1o : o1 < 4) (h1q : q1 < 4) (h2o : o2 < 4) (h2q : q2 < 4)
    (h3o : o3 < 4) (h3q : q3 < 4) (h4o : o4 < 4) (h4q : q4 < 4) :
    cellMin (gadd o0 q0) (gadd o3 q3) (gadd o4 q4)
      ≤ wt5N (gadd o0 q0) (gadd o1 q1) (gadd o2 q2) (gadd o3 q3) (gadd o4 q4) := by
  have h := cellMin_le ⟨gadd o0 q0, gadd_lt_two h0o h0q⟩ ⟨gadd o1 q1, gadd_lt_four h1o h1q⟩
    ⟨gadd o2 q2, gadd_lt_four h2o h2q⟩ ⟨gadd o3 q3, gadd_lt_four h3o h3q⟩
    ⟨gadd o4 q4, gadd_lt_four h4o h4q⟩
  simpa using h

/-- Per-cell **relaxed** soundness on actual coset values: `rcell` of the (offset-shifted)
comps 0,3,4 with the comp-1,2 offsets and raw supports lower-bounds the exact `wt5N`. -/
theorem cell_relaxed_sound' {o0 q0 o1 q1 o2 q2 o3 q3 o4 q4 : Nat}
    (h0o : o0 < 2) (h0q : q0 < 2) (h1o : o1 < 4) (h1q : q1 < 4) (h2o : o2 < 4) (h2q : q2 < 4)
    (h3o : o3 < 4) (h3q : q3 < 4) (h4o : o4 < 4) (h4q : q4 < 4) :
    rcell (gadd o0 q0) (gadd o3 q3) (gadd o4 q4) o1 o2 (supp q1) (supp q2)
      ≤ wt5N (gadd o0 q0) (gadd o1 q1) (gadd o2 q2) (gadd o3 q3) (gadd o4 q4) := by
  have h := rcell_le ⟨gadd o0 q0, gadd_lt_two h0o h0q⟩ ⟨gadd o3 q3, gadd_lt_four h3o h3q⟩
    ⟨gadd o4 q4, gadd_lt_four h4o h4q⟩ ⟨o1, h1o⟩ ⟨o2, h2o⟩ ⟨q1, h1q⟩ ⟨q2, h2q⟩
  simpa using h

/-! ## §10 The finite engine: per-cell accessors and the three cost layers

`ov o j s` reads seam-offset CRT component `j` at slot `s`; `pv G k s side` reads Γ-array
`G`'s `k`-th pair at slot `s`, side `side` (0 = A-block/left, 1 = B-block/right).  The three
cost layers are explicit eight-cell sums (four `Z₂²` slots × two sides) so the monotone
soundness (§11) sums them cell-by-cell. -/

/-- Seam-offset CRT component `j` at slot `s` (`o` is a flat `j*4+s` table). -/
@[inline] def ov (o : Array Nat) (j s : Nat) : Nat := o.getD (j*4+s) 0

/-- Γ-array `G`'s `k`-th pair value at slot `s`, side `side` (flat `k*8+side*4+s`). -/
@[inline] def pv (G : Array Nat) (k s side : Nat) : Nat := G.getD (k*8+side*4+s) 0

/-- One slab-min cell: `cellMin` of the offset-shifted comps 0,3,4 at `(s, side)`. -/
def slabCell (o : Array Nat) (a0 a3 a4 s side : Nat) : Nat :=
  cellMin (gadd (ov o 0 s) (pv G0gen a0 s side)) (gadd (ov o 3 s) (pv G3gen a3 s side))
          (gadd (ov o 4 s) (pv G4gen a4 s side))

/-- One exact cell: `wt5N` of the five offset-shifted comps at `(s, side)`. -/
def exCell (o : Array Nat) (a0 a3 a4 s side k1 k2 : Nat) : Nat :=
  wt5N (gadd (ov o 0 s) (pv G0gen a0 s side)) (gadd (ov o 1 s) (pv F1gen k1 s side))
       (gadd (ov o 2 s) (pv F2gen k2 s side)) (gadd (ov o 3 s) (pv G3gen a3 s side))
       (gadd (ov o 4 s) (pv G4gen a4 s side))

/-- One relaxed cell: offset-aware `rcell` of comps 0,3,4 with class masks `cm1,cm2`. -/
def relaxCell (o : Array Nat) (a0 a3 a4 s side cm1 cm2 : Nat) : Nat :=
  rcell (gadd (ov o 0 s) (pv G0gen a0 s side)) (gadd (ov o 3 s) (pv G3gen a3 s side))
        (gadd (ov o 4 s) (pv G4gen a4 s side)) (ov o 1 s) (ov o 2 s)
        ((cm1 >>> s) &&& 1) ((cm2 >>> s) &&& 1)

/-- The slab-min lower bound over all eight `(side, slot)` cells. -/
def slabMin (oL oR : Array Nat) (a0 a3 a4 : Nat) : Nat :=
  slabCell oL a0 a3 a4 0 0 + slabCell oR a0 a3 a4 0 1
  + slabCell oL a0 a3 a4 1 0 + slabCell oR a0 a3 a4 1 1
  + slabCell oL a0 a3 a4 2 0 + slabCell oR a0 a3 a4 2 1
  + slabCell oL a0 a3 a4 3 0 + slabCell oR a0 a3 a4 3 1

/-- The exact coset weight over all eight `(side, slot)` cells (fibers `k1,k2` into Γ₁,Γ₂). -/
def exCost (oL oR : Array Nat) (a0 a3 a4 k1 k2 : Nat) : Nat :=
  exCell oL a0 a3 a4 0 0 k1 k2 + exCell oR a0 a3 a4 0 1 k1 k2
  + exCell oL a0 a3 a4 1 0 k1 k2 + exCell oR a0 a3 a4 1 1 k1 k2
  + exCell oL a0 a3 a4 2 0 k1 k2 + exCell oR a0 a3 a4 2 1 k1 k2
  + exCell oL a0 a3 a4 3 0 k1 k2 + exCell oR a0 a3 a4 3 1 k1 k2

/-- The relaxed lower bound over all eight cells (comp-1,2 support classes `m1L/R, m2L/R`). -/
def relaxed (oL oR : Array Nat) (a0 a3 a4 m1L m1R m2L m2R : Nat) : Nat :=
  relaxCell oL a0 a3 a4 0 0 m1L m2L + relaxCell oR a0 a3 a4 0 1 m1R m2R
  + relaxCell oL a0 a3 a4 1 0 m1L m2L + relaxCell oR a0 a3 a4 1 1 m1R m2R
  + relaxCell oL a0 a3 a4 2 0 m1L m2L + relaxCell oR a0 a3 a4 2 1 m1R m2R
  + relaxCell oL a0 a3 a4 3 0 m1L m2L + relaxCell oR a0 a3 a4 3 1 m1R m2R

/-- Fiber phase: every `(k1,k2)` in support classes `(i1,i2)` has exact weight `≥ 12`. -/
def fiberOK (oL oR : Array Nat) (a0 a3 a4 i1 i2 : Nat) : Bool :=
  let lo1 := F1off.getD i1 0; let hi1 := F1off.getD (i1+1) 0
  let lo2 := F2off.getD i2 0; let hi2 := F2off.getD (i2+1) 0
  (List.range (hi1-lo1)).all (fun d1 =>
    (List.range (hi2-lo2)).all (fun d2 =>
      decide (12 ≤ exCost oL oR a0 a3 a4 (lo1+d1) (lo2+d2))))

/-- Two-phase check on a live slab: each support class is relaxed-certified or fiber-checked. -/
def liveOK (oL oR : Array Nat) (a0 a3 a4 : Nat) : Bool :=
  (List.range nC1).all (fun i1 =>
    (List.range nC2).all (fun i2 =>
      let rc := relaxed oL oR a0 a3 a4 (F1mL.getD i1 0) (F1mR.getD i1 0)
                                       (F2mL.getD i2 0) (F2mR.getD i2 0)
      (12 ≤ rc) || fiberOK oL oR a0 a3 a4 i1 i2))

/-- The floor decision: every `(comp 0,3,4)` slab is slab-min-certified or two-phase-OK. -/
def floorOK (oL oR : Array Nat) : Bool :=
  (List.range nG0).all (fun a0 =>
    (List.range nG3).all (fun a3 =>
      (List.range nG4).all (fun a4 =>
        (12 ≤ slabMin oL oR a0 a3 a4) || liveOK oL oR a0 a3 a4)))

/-! ## §11 The monotone soundness: `slabMin`/`relaxed` lower-bound `exCost`

The eight-cell sums are summed cell-by-cell: each cell's bound is the per-cell bridge (§9),
and `omega` adds the eight inequalities.  The data bounds (`pv` entries `< 2` for comp 0,
`< 4` otherwise; offsets passed in) are discharged by `native_decide` over the arrays. -/

/-- Default-`0` `getD` access stays `< b` when every in-range entry is and `0 < b`. -/
theorem getD_lt {a : Array Nat} {b : Nat} (hb : 0 < b)
    (hin : ∀ i, (h : i < a.size) → a[i] < b) (i : Nat) : a.getD i 0 < b := by
  unfold Array.getD
  split
  · next h => exact hin i h
  · exact hb

/-- Γ-array entry bound from an all-entries bound (`pv` is a `getD`). -/
theorem pv_lt {G : Array Nat} {b : Nat} (hb : 0 < b)
    (hin : ∀ i, (h : i < G.size) → G[i] < b) (k s side : Nat) : pv G k s side < b :=
  getD_lt hb hin (k*8+side*4+s)

theorem pv_G0_lt2 (k s side : Nat) : pv G0gen k s side < 2 :=
  pv_lt (by norm_num) (by native_decide) k s side
theorem pv_G3_lt4 (k s side : Nat) : pv G3gen k s side < 4 :=
  pv_lt (by norm_num) (by native_decide) k s side
theorem pv_G4_lt4 (k s side : Nat) : pv G4gen k s side < 4 :=
  pv_lt (by norm_num) (by native_decide) k s side
theorem pv_F1_lt4 (k s side : Nat) : pv F1gen k s side < 4 :=
  pv_lt (by norm_num) (by native_decide) k s side
theorem pv_F2_lt4 (k s side : Nat) : pv F2gen k s side < 4 :=
  pv_lt (by norm_num) (by native_decide) k s side

/-- Offset CRT component `< 4` from an all-entries bound (`ov` is a `getD`). -/
theorem ov_lt4 {o : Array Nat} (ho4 : ∀ i, o.getD i 0 < 4) (j s : Nat) : ov o j s < 4 :=
  ho4 (j*4+s)

/-- Per-cell **slab-min** monotonicity: one cell's slab-min `≤` its exact weight. -/
theorem slabCell_le_exCell (o : Array Nat) (a0 a3 a4 s side k1 k2 : Nat)
    (ho4 : ∀ i, o.getD i 0 < 4) (ho0 : ov o 0 s < 2) :
    slabCell o a0 a3 a4 s side ≤ exCell o a0 a3 a4 s side k1 k2 := by
  unfold slabCell exCell
  exact cell_slab_sound ho0 (pv_G0_lt2 a0 s side)
    (ov_lt4 ho4 1 s) (pv_F1_lt4 k1 s side) (ov_lt4 ho4 2 s) (pv_F2_lt4 k2 s side)
    (ov_lt4 ho4 3 s) (pv_G3_lt4 a3 s side) (ov_lt4 ho4 4 s) (pv_G4_lt4 a4 s side)

/-- Per-cell **relaxed** monotonicity: one cell's relaxed bound `≤` its exact weight, given
the class masks `cm1,cm2` agree with the fiber entry's raw supports at this slot. -/
theorem relaxCell_le_exCell (o : Array Nat) (a0 a3 a4 s side k1 k2 cm1 cm2 : Nat)
    (ho4 : ∀ i, o.getD i 0 < 4) (ho0 : ov o 0 s < 2)
    (hm1 : (cm1 >>> s) &&& 1 = supp (pv F1gen k1 s side))
    (hm2 : (cm2 >>> s) &&& 1 = supp (pv F2gen k2 s side)) :
    relaxCell o a0 a3 a4 s side cm1 cm2 ≤ exCell o a0 a3 a4 s side k1 k2 := by
  unfold relaxCell exCell
  rw [hm1, hm2]
  exact cell_relaxed_sound' ho0 (pv_G0_lt2 a0 s side)
    (ov_lt4 ho4 1 s) (pv_F1_lt4 k1 s side) (ov_lt4 ho4 2 s) (pv_F2_lt4 k2 s side)
    (ov_lt4 ho4 3 s) (pv_G3_lt4 a3 s side) (ov_lt4 ho4 4 s) (pv_G4_lt4 a4 s side)

/-- **Slab-min monotonicity**: `slabMin ≤ exCost` for every fiber `(k1,k2)`. -/
theorem slabMin_le_exCost (oL oR : Array Nat) (a0 a3 a4 k1 k2 : Nat)
    (hoL4 : ∀ i, oL.getD i 0 < 4) (hoR4 : ∀ i, oR.getD i 0 < 4)
    (hoL0 : ∀ s, s < 4 → ov oL 0 s < 2) (hoR0 : ∀ s, s < 4 → ov oR 0 s < 2) :
    slabMin oL oR a0 a3 a4 ≤ exCost oL oR a0 a3 a4 k1 k2 := by
  have c0L := slabCell_le_exCell oL a0 a3 a4 0 0 k1 k2 hoL4 (hoL0 0 (by norm_num))
  have c0R := slabCell_le_exCell oR a0 a3 a4 0 1 k1 k2 hoR4 (hoR0 0 (by norm_num))
  have c1L := slabCell_le_exCell oL a0 a3 a4 1 0 k1 k2 hoL4 (hoL0 1 (by norm_num))
  have c1R := slabCell_le_exCell oR a0 a3 a4 1 1 k1 k2 hoR4 (hoR0 1 (by norm_num))
  have c2L := slabCell_le_exCell oL a0 a3 a4 2 0 k1 k2 hoL4 (hoL0 2 (by norm_num))
  have c2R := slabCell_le_exCell oR a0 a3 a4 2 1 k1 k2 hoR4 (hoR0 2 (by norm_num))
  have c3L := slabCell_le_exCell oL a0 a3 a4 3 0 k1 k2 hoL4 (hoL0 3 (by norm_num))
  have c3R := slabCell_le_exCell oR a0 a3 a4 3 1 k1 k2 hoR4 (hoR0 3 (by norm_num))
  simp only [slabMin, exCost]
  omega

/-- **Relaxed monotonicity**: `relaxed ≤ exCost` for every fiber `(k1,k2)` whose raw supports
match the class masks at all four slots. -/
theorem relaxed_le_exCost (oL oR : Array Nat) (a0 a3 a4 k1 k2 m1L m1R m2L m2R : Nat)
    (hoL4 : ∀ i, oL.getD i 0 < 4) (hoR4 : ∀ i, oR.getD i 0 < 4)
    (hoL0 : ∀ s, s < 4 → ov oL 0 s < 2) (hoR0 : ∀ s, s < 4 → ov oR 0 s < 2)
    (hm1L : ∀ s, s < 4 → (m1L >>> s) &&& 1 = supp (pv F1gen k1 s 0))
    (hm1R : ∀ s, s < 4 → (m1R >>> s) &&& 1 = supp (pv F1gen k1 s 1))
    (hm2L : ∀ s, s < 4 → (m2L >>> s) &&& 1 = supp (pv F2gen k2 s 0))
    (hm2R : ∀ s, s < 4 → (m2R >>> s) &&& 1 = supp (pv F2gen k2 s 1)) :
    relaxed oL oR a0 a3 a4 m1L m1R m2L m2R ≤ exCost oL oR a0 a3 a4 k1 k2 := by
  have c0L := relaxCell_le_exCell oL a0 a3 a4 0 0 k1 k2 m1L m2L hoL4 (hoL0 0 (by norm_num))
    (hm1L 0 (by norm_num)) (hm2L 0 (by norm_num))
  have c0R := relaxCell_le_exCell oR a0 a3 a4 0 1 k1 k2 m1R m2R hoR4 (hoR0 0 (by norm_num))
    (hm1R 0 (by norm_num)) (hm2R 0 (by norm_num))
  have c1L := relaxCell_le_exCell oL a0 a3 a4 1 0 k1 k2 m1L m2L hoL4 (hoL0 1 (by norm_num))
    (hm1L 1 (by norm_num)) (hm2L 1 (by norm_num))
  have c1R := relaxCell_le_exCell oR a0 a3 a4 1 1 k1 k2 m1R m2R hoR4 (hoR0 1 (by norm_num))
    (hm1R 1 (by norm_num)) (hm2R 1 (by norm_num))
  have c2L := relaxCell_le_exCell oL a0 a3 a4 2 0 k1 k2 m1L m2L hoL4 (hoL0 2 (by norm_num))
    (hm1L 2 (by norm_num)) (hm2L 2 (by norm_num))
  have c2R := relaxCell_le_exCell oR a0 a3 a4 2 1 k1 k2 m1R m2R hoR4 (hoR0 2 (by norm_num))
    (hm1R 2 (by norm_num)) (hm2R 2 (by norm_num))
  have c3L := relaxCell_le_exCell oL a0 a3 a4 3 0 k1 k2 m1L m2L hoL4 (hoL0 3 (by norm_num))
    (hm1L 3 (by norm_num)) (hm2L 3 (by norm_num))
  have c3R := relaxCell_le_exCell oR a0 a3 a4 3 1 k1 k2 m1R m2R hoR4 (hoR0 3 (by norm_num))
    (hm1R 3 (by norm_num)) (hm2R 3 (by norm_num))
  simp only [relaxed, exCost]
  omega

end Quantum.Stabilizer.Homological.BB.LightStab
