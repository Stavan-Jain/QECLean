/-
# Phase 6: the safe-sector confined floor — the native-decidable engine

`MImClassify` reduced the safe-sector weight to `costFromComps` of the ten coset
components `seam offset ⊕ engine-multiplied free datum` (§6, §7).  This module builds
the **finite engine** that decides the floor `≥ 12` over the (2³⁰) coset product:

* the Nat-encoded per-cell cost (`wt5N`, reusing `WT5_TABLE`), the relaxed d₃ table
  (`d3`), and the slab-min `cellMin` (the per-cell minimum over comps 1,2 support);
* the **soundness keystones** (`cellMin_le`, `d3_le`): the slab-min and the relaxed
  d₃ are valid LOWER bounds on the exact layer weight, finite-checked over the 512
  value-tuples.  These are what make the slab-min filter — which certifies ~97 % of
  the 16384 `(comp 0,3,4)` slabs in 32 lookups, leaving only ~400–1020 "live" slabs
  per orbit for the two-phase fiber check — a *sound* reduction of the full product.

The `floorOK` Bool (slab-filter + two-phase) and its per-orbit `native_decide`
(validated: `true` for all five orbits, 17–44 s; see `scripts/gen_floor_lean.py`)
are assembled on top of these primitives.  Convention: a ring element is its four
`Z₂²`-slot values in `allS` order `(0,0),(1,0),(0,1),(1,1)`; F₄ add is bitwise xor
on the 2-bit `.val` encoding (`gadd = fadd` on `.val`).
-/
import QEC.Stabilizer.Codes.BivariateBicycle.MImClassify

open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

/-! ## §8 The Nat-encoded cost primitives and the soundness keystones -/

/-- F₄ add on the Nat encoding `0..3` (= bitwise xor = `fadd` on `.val`). -/
@[inline] def gadd (a b : Nat) : Nat := a ^^^ b

/-- `wt5OfComps` on Nat indices (`WT5_TABLE` reused, so `wt5N (·.val) = wt5OfComps`). -/
@[inline] def wt5N (v0 v1 v2 v3 v4 : Nat) : Nat :=
  WT5_TABLE.getD (v0 + 2 * (v1 + 4 * (v2 + 4 * (v3 + 4 * v4)))) 99

/-- The relaxed per-cell d₃ table (comps 0,3,4 value-exact; comps 1,2 by support
`(a1,a2)`): `d3 v0 v3 v4 a1 a2 = min weight3` over layers with comps 0,3,4 `= (v0,v3,v4)`
and comps 1,2 alive iff `(a1,a2)`. -/
def D3V : Array Nat :=
  #[0,6,6,4,6,4,4,2,6,4,4,2,6,4,4,2,6,4,4,2,4,2,2,4,4,2,2,4,4,2,2,4,6,4,4,2,4,2,2,4,
    4,2,2,4,4,2,2,4,6,4,4,2,4,2,2,4,4,2,2,4,4,2,2,4,9,3,3,5,3,5,5,3,3,5,5,3,3,5,5,3,
    3,5,5,3,5,3,3,1,5,3,3,1,5,3,3,1,3,5,5,3,5,3,3,1,5,3,3,1,5,3,3,1,3,5,5,3,5,3,3,1,
    5,3,3,1,5,3,3,1]

@[inline] def d3 (v0 v3 v4 a1 a2 : Nat) : Nat := D3V.getD ((v0*16+v3*4+v4)*4+a1+2*a2) 99

/-- Per-cell slab-min: the min d₃ over the two support bits (comps 1,2 free). -/
@[inline] def cellMin (v0 v3 v4 : Nat) : Nat :=
  min (min (d3 v0 v3 v4 0 0) (d3 v0 v3 v4 1 0)) (min (d3 v0 v3 v4 0 1) (d3 v0 v3 v4 1 1))

/-- Support bit of a Nat value. -/
@[inline] def supp (v : Nat) : Nat := if v == 0 then 0 else 1

/-- **Slab-min soundness keystone**: the per-cell slab-min lower-bounds the exact layer
weight for every choice of the comp-1,2 values.  (Finite check over the 512 value-tuples;
`v0 ∈ Fin 2` since comp 0 is the trivial-character, `F₂`-valued component.) -/
theorem cellMin_le : ∀ (v0 : Fin 2) (v1 v2 v3 v4 : Fin 4),
    cellMin v0.val v3.val v4.val ≤ wt5N v0.val v1.val v2.val v3.val v4.val := by
  native_decide

/-- **Relaxed soundness keystone**: the relaxed d₃ (comps 1,2 by their actual support)
lower-bounds the exact layer weight. -/
theorem d3_le : ∀ (v0 : Fin 2) (v1 v2 v3 v4 : Fin 4),
    d3 v0.val v3.val v4.val (supp v1.val) (supp v2.val)
      ≤ wt5N v0.val v1.val v2.val v3.val v4.val := by
  native_decide

/-! ## §9 The per-cell soundness bridge (keystone applied to coset values)

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

/-- Per-cell **relaxed** soundness on actual coset values (comps 1,2 by their support). -/
theorem cell_relaxed_sound {o0 q0 o1 q1 o2 q2 o3 q3 o4 q4 : Nat}
    (h0o : o0 < 2) (h0q : q0 < 2) (h1o : o1 < 4) (h1q : q1 < 4) (h2o : o2 < 4) (h2q : q2 < 4)
    (h3o : o3 < 4) (h3q : q3 < 4) (h4o : o4 < 4) (h4q : q4 < 4) :
    d3 (gadd o0 q0) (gadd o3 q3) (gadd o4 q4) (supp (gadd o1 q1)) (supp (gadd o2 q2))
      ≤ wt5N (gadd o0 q0) (gadd o1 q1) (gadd o2 q2) (gadd o3 q3) (gadd o4 q4) := by
  have h := d3_le ⟨gadd o0 q0, gadd_lt_two h0o h0q⟩ ⟨gadd o1 q1, gadd_lt_four h1o h1q⟩
    ⟨gadd o2 q2, gadd_lt_four h2o h2q⟩ ⟨gadd o3 q3, gadd_lt_four h3o h3q⟩
    ⟨gadd o4 q4, gadd_lt_four h4o h4q⟩
  simpa using h

end Quantum.Stabilizer.Homological.BB.LightStab
