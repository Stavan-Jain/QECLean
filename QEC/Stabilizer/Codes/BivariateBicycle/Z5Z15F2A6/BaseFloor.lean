/-
# A21: the logical base floor `LogicalFloor 8` for the `[[150,8,8]]` base

Discharges (in progress) the `hbase : coverData.LogicalFloor 8`
hypothesis of `cover300_pauli_distance_eq_16_of_classification`
(`Distance.lean`) — the `d(base) ≥ 8` half of `d(base) = 8`, currently
certified offline by CaDiCaL `UNSAT@7`.

Proof architecture (the analytic split map of
`qec-lab:experiments/bb_lab/notes/A21_analytic_base_floor.md` §3):

* **weights 1,3,5,7** — parity (PAR): `ε(A) = ε(B) = 1` forces
  `|u_L| ≡ |u_R| (mod 2)`;
* **weights 2,4** — the parametric small-cycle bundle
  (`SmallCycleData`, `Framework/Homological/BBSmallCycle.lean`), whose
  finite obligations are discharged below by `native_decide`
  (BB108/BB90/Z6Z14 pattern);
* **weight 6** — the new depth layer: every weight-6 cycle is a
  boundary (in fact a generator column `∂₂δ_g = (A+g, B+g)`).  The
  analytic proof stratifies by the split `(|u_L|, |u_R|)`:
  one-sided splits die on `μ(Ann) = 40` (single shared `F₁₆` orbit;
  all 15 nonzero annihilator elements are translates of the trace
  idempotent, weight `5·8 = 40`); `(1,5)/(5,1)` die on the y-span
  lemma (row-block analysis of `A⋆T` under `A = 1+x+y` against `B`'s
  row span 6 / min gap 2); `(2,4)/(4,2)` and `(2,2)` die on
  D2-pigeonholes and word-metric spread bounds; `(3,3)` is classified
  via transversality + the overlap lemma
  (mult-≥3 values of `d(A⊖B)` = `dA ∪ dB`), forcing the generator
  column.  Machine confirmations:
  `qec-lab:experiments/bb_lab/scripts/a21_numeric_*.py`.

Current state: the weight-≤5 layer and the assembly are complete; the
weight-6 classification is stated (`weight6_cycle_is_boundary`) and
`sorry`-marked pending the session-2 formalization of the split map.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Defs
import QEC.Stabilizer.Framework.Homological.BBSmallCycle

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

set_option maxRecDepth 4096

/-! ## The small-cycle bundle (weights 2 and 4)

Same shape as `BaseFloors/BB108.lean`; note this instance is OUTSIDE
the A16 class ((iii) fails — `A = 1+x+y` is monomial in both parity
projections), so the bundle's finite checks are doing real per-instance
work here, not just certifying a class member. -/

/-- `ε(A) = 1`. -/
lemma epsA_holds : ∑ h : G150, a150 h = 1 := by native_decide

/-- `ε(B) = 1`. -/
lemma epsB_holds : ∑ h : G150, b150 h = 1 := by native_decide

/-- No normalized weight-2 cycle. -/
lemma check_two_holds : ∀ b : Fin 2, ∀ q : G150 × Fin 2,
    q ≠ ((0 : G150), b) →
    ∃ h : G150, SmallCycle.termAt a150 b150 ((0 : G150), b) h
      + SmallCycle.termAt a150 b150 q h ≠ 0 := by
  native_decide

/-- No normalized weight-4 cycle (tuple form; colliding tuples cancel to
the weight-2 shape). -/
lemma check_four_holds : ∀ b : Fin 2, ∀ q₁ q₂ q₃ : G150 × Fin 2,
    q₁ = ((0 : G150), b) ∨ q₂ = ((0 : G150), b) ∨
    q₃ = ((0 : G150), b) ∨
    ∃ h : G150, SmallCycle.termAt a150 b150 ((0 : G150), b) h
      + SmallCycle.termAt a150 b150 q₁ h
      + SmallCycle.termAt a150 b150 q₂ h
      + SmallCycle.termAt a150 b150 q₃ h ≠ 0 := by
  native_decide

/-- The small-cycle bundle for the `[[150,8,8]]` base. -/
def floorData : SmallCycleData G150 where
  A := a150
  B := b150
  epsA := epsA_holds
  epsB := epsB_holds
  check_two := check_two_holds
  check_four := check_four_holds

lemma floorData_complex : floorData.complex = base150Complex := rfl

/-- **Strong small-cycle floor**: every nonzero 1-cycle of the base
complex has weight ≥ 6 — boundaries included.  (Sharp: the generator
columns have weight exactly 6.) -/
theorem strong_floor (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0) (hne : u ≠ 0) :
    6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card :=
  floorData.cycle_weight_ge_6 u hcyc hne

/-! ## The weight-6 layer (the A21 depth rung)

The classification target: the only weight-6 cycles are the 75
generator columns `∂₂δ_g`, hence boundaries.  Session-2 split map:

* one-sided `(6,0)/(0,6)`: `μ(Ann A) = μ(Ann B) = 40` via a
  `KernelCert`-style pivot certificate + a 16-element weight table;
* `(1,5)/(5,1)`: the y-span lemma (row recurrence
  `(A⋆T)_v = (1+x)T_v + T_{v−1}`, block analysis vs `B`'s row gaps);
* `(2,2)/(2,4)/(4,2)`: D2-pigeonholes + σ pair tables (tiny decides);
* `(3,3)`: transversality + overlap-lemma localization to
  `{±A+t} × {±B+s}`, row-invariant kills of the non-generator combos.
-/

/-- **Weight-6 classification** (statement): every weight-6 1-cycle of
the base complex is a boundary. -/
theorem weight6_cycle_is_boundary (u : G150 × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn a150 b150 u = 0)
    (hw : (Finset.univ.filter fun p => u p ≠ 0).card = 6) :
    u ∈ base150Complex.boundaries := by
  sorry  -- TODO(a21-w6): split map (3,3)→generator column; see note §3.7

/-! ## Assembly: the logical floor -/

/-- `chainWeight` on the cover bundle's base complex, in raw `Finset`
form (definitional; the `maxRecDepth` bump covers the projection
chain). -/
lemma baseComplex_chainWeight_eq (u : G150 × Fin 2 → ZMod 2) :
    coverData.baseComplex.chainWeight u
      = (Finset.univ.filter fun p : G150 × Fin 2 => u p ≠ 0).card := rfl

/-- **The logical base floor**: every non-boundary 1-cycle of the
`[[150,8,8]]` base complex has weight ≥ 8.  This is the
`hbase` hypothesis of `cover300_pauli_distance_eq_16_of_classification`.

Proof: parity kills odd weights; the strong small-cycle floor kills
nonzero weights ≤ 5; the weight-6 classification shows weight-6 cycles
are boundaries; hence a non-boundary cycle weighs ≥ 8. -/
theorem logicalFloor_8 : coverData.LogicalFloor 8 := by
  intro u hcyc hnb
  rw [baseComplex_chainWeight_eq]
  by_contra hlt
  push Not at hlt
  have hne : u ≠ 0 := by
    rintro rfl
    exact hnb (zero_mem _)
  have hcyc' : bbBoundary1Fn a150 b150 u = 0 := hcyc
  have h6 : 6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card :=
    strong_floor u hcyc' hne
  have hpar : (Finset.univ.filter fun p => u p ≠ 0).card % 2 = 0 :=
    floorData.cycle_weight_even u hcyc'
  have hw : (Finset.univ.filter fun p => u p ≠ 0).card = 6 := by omega
  -- `coverData.baseComplex = base150Complex` is definitional, so the
  -- boundary memberships coincide (no `rw` — the membership type depends
  -- on the complex, which breaks the rewrite motive).
  exact hnb (show u ∈ coverData.baseComplex.boundaries from
    weight6_cycle_is_boundary u hcyc' hw)

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
