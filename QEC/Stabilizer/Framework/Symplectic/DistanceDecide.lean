module

public import QEC.Stabilizer.Framework.Symplectic.Presentation
public import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
public import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# Distance of a presented code by `decide`

For a code given by a literal `StabilizerCode.Presentation`, the distance is a
finite check: exhibit one nontrivial logical operator of weight `d`, and show
that no Pauli of weight `1, …, d − 1` is a nontrivial logical. This file turns
both halves into closed propositions that `decide` settles, so that

```lean
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  presentation.hasCodeDistance_of_decide σ[IYYIX] (by decide +kernel) (by decide +kernel)
```

is the whole distance proof of a small code, CSS or not, degenerate or not.
Use `decide +kernel`: the elaborator's `decide` runs out of recursion depth on
the span checks of anything larger than a handful of generators.

- `NQubitPauliOperator.ofWeight n w`: every operator of weight `w`, listed
  (`mem_ofWeight`). The lower bound ranges over these lists rather than over
  all `4 ^ n` operators.
- `InSpan L op`: the symplectic vector of `op` is a combination of the rows of
  the check matrix of `L`, i.e. `op` is a stabilizer up to phase
  (`inSpan_iff`). Decided by trying all `2 ^ L.length` combinations.
- `Harmless L op`: some element of `L` anticommutes with `op`, or `op` is in
  the span. A harmless operator is never a nontrivial logical
  (`not_isNontrivialLogicalOperator_of_harmless`). The second disjunct is what
  makes degenerate codes (Shor's) go through unchanged: the low-weight Paulis
  no check detects are stabilizers.
- `NoLogicalBelow L d`: every operator of weight `1, …, d − 1` is harmless.
- `IsLogicalWitness L d g`: `g` has weight `d`, commutes with `L`, and is not
  in the span. Such a `g` is a nontrivial logical
  (`isNontrivialLogicalOperator_of_isLogicalWitness`); no anticommuting partner
  is needed.
- `StabilizerCode.Presentation.hasCodeDistance_of_decide`: the closer.

The checks are stated with the symplectic inner product of operator parts, so
the kernel never multiplies group elements or tracks phases. Their `Decidable`
instances are given explicitly, pinned to `List.decidableBAll` /
`List.decidableBEx`: `NQubitPauliOperator n` is a `Fintype`, and an instance
found by search would enumerate all `4 ^ n` operators.

The cost of the lower bound is `∑_{w < d} C(n, w) · 3 ^ w` patterns, each tested
against the generators, plus one span check per undetected pattern. That is
comfortable for the small literal codes; larger codes want a packed-`Nat`
version of the same predicates.
-/

@[expose] public section

namespace Quantum

variable {n k : ℕ}

namespace NQubitPauliOperator

/-! ## Listing the operators of a given weight -/

/-- Prepend a qubit carrying `P` to an `n`-qubit operator. -/
def cons (P : PauliOperator) (t : NQubitPauliOperator n) : NQubitPauliOperator (n + 1) :=
  Fin.cons (α := fun _ => PauliOperator) P t

@[simp] lemma cons_zero (P : PauliOperator) (t : NQubitPauliOperator n) : cons P t 0 = P :=
  rfl

@[simp] lemma cons_succ (P : PauliOperator) (t : NQubitPauliOperator n) (i : Fin n) :
    cons P t i.succ = t i :=
  rfl

/-- Every `(n + 1)`-qubit operator is its first qubit prepended to the rest. -/
lemma cons_self_tail (op : NQubitPauliOperator (n + 1)) :
    cons (op 0) (fun i => op i.succ) = op :=
  Fin.cons_self_tail (α := fun _ => PauliOperator) op

/-- Prepending `P` adds one to the weight iff `P` is not the identity. -/
lemma weight_cons (P : PauliOperator) (t : NQubitPauliOperator n) :
    weight (cons P t) = (if P = .I then 0 else 1) + weight t := by
  simp only [weight, support, Finset.card_filter, Fin.sum_univ_succ, cons_zero, cons_succ, ite_not]
  congr 1

/-- The operators of weight `w` on `n` qubits, built qubit by qubit: the first
qubit is `I` and the rest has weight `w`, or it is `X`, `Y` or `Z` and the rest
has weight `w - 1`. -/
def ofWeight : (n w : ℕ) → List (NQubitPauliOperator n)
  | 0, 0 => [fun i => i.elim0]
  | 0, _ + 1 => []
  | n + 1, 0 => (ofWeight n 0).map (cons .I)
  | n + 1, w + 1 =>
      (ofWeight n (w + 1)).map (cons .I) ++
        [PauliOperator.X, .Y, .Z].flatMap fun P => (ofWeight n w).map (cons P)

/-- Every operator appears in the list of its weight. -/
theorem mem_ofWeight : ∀ {n : ℕ} (op : NQubitPauliOperator n), op ∈ ofWeight n (weight op)
  | 0, op => by
    have h : op = fun i => i.elim0 := funext fun i => i.elim0
    subst h
    exact List.mem_singleton_self _
  | n + 1, op => by
    rw [← cons_self_tail op, weight_cons]
    have ih := mem_ofWeight (fun i : Fin n => op i.succ)
    generalize hP : op 0 = P
    generalize ht : (fun i : Fin n => op i.succ) = t at ih
    cases P with
    | I =>
      simp only [↓reduceIte, Nat.zero_add]
      rcases hw : weight t with _ | w <;> rw [hw] at ih
      · exact List.mem_map_of_mem ih
      · exact List.mem_append_left _ (List.mem_map_of_mem ih)
    | X | Y | Z =>
      simp only [reduceCtorEq, ↓reduceIte, Nat.add_comm 1 (weight t)]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, by simp, List.mem_map_of_mem ih⟩)

end NQubitPauliOperator

namespace StabilizerGroup

open NQubitPauliGroupElement NQubitPauliOperator

/-! ## The decidable predicates -/

/-- The symplectic vector of `op` is a combination of the check-matrix rows of
`L`. -/
def InSpan (L : List (NQubitPauliGroupElement n)) (op : NQubitPauliOperator n) : Prop :=
  ∃ f : Fin L.length → ZMod 2, ∑ i, f i • (checkMatrix L).row i = toSymplectic op

/-- `InSpan` is decided by trying every combination of rows. -/
instance (L : List (NQubitPauliGroupElement n)) (op : NQubitPauliOperator n) :
    Decidable (InSpan L op) :=
  Fintype.decidableExistsFintype

lemma inSpan_iff (L : List (NQubitPauliGroupElement n)) (op : NQubitPauliOperator n) :
    InSpan L op ↔ toSymplectic op ∈ sympSpan L :=
  (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).symm

/-- `op` is no threat to the distance: some element of `L` anticommutes with
it, or it is a stabilizer up to phase. -/
def Harmless (L : List (NQubitPauliGroupElement n)) (op : NQubitPauliOperator n) : Prop :=
  (∃ s ∈ L, symplecticInner op s.operators = 1) ∨ InSpan L op

instance (L : List (NQubitPauliGroupElement n)) (op : NQubitPauliOperator n) :
    Decidable (Harmless L op) :=
  @instDecidableOr _ _ (List.decidableBEx _ L) inferInstance

/-- Every operator of weight `1, …, d − 1` is harmless. -/
def NoLogicalBelow (L : List (NQubitPauliGroupElement n)) (d : ℕ) : Prop :=
  ∀ w ∈ List.range' 1 (d - 1), ∀ op ∈ ofWeight n w, Harmless L op

instance (L : List (NQubitPauliGroupElement n)) (d : ℕ) : Decidable (NoLogicalBelow L d) :=
  @List.decidableBAll _ (fun w => ∀ op ∈ ofWeight n w, Harmless L op)
    (fun w => List.decidableBAll _ (ofWeight n w)) _

/-- `g` has weight `d`, commutes with every element of `L`, and is not a
stabilizer up to phase. -/
def IsLogicalWitness (L : List (NQubitPauliGroupElement n)) (d : ℕ)
    (g : NQubitPauliGroupElement n) : Prop :=
  weight g = d ∧ (∀ s ∈ L, symplecticInner g.operators s.operators = 0) ∧
    ¬InSpan L g.operators

instance (L : List (NQubitPauliGroupElement n)) (d : ℕ) (g : NQubitPauliGroupElement n) :
    Decidable (IsLogicalWitness L d g) :=
  @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ (List.decidableBAll _ L)
    inferInstance)

/-! ## Soundness -/

section Soundness

variable {L : List (NQubitPauliGroupElement n)} {S : StabilizerGroup n}

/-- A harmless operator part never belongs to a nontrivial logical: a detected
one is outside the centralizer, an in-span one is a stabilizer's. -/
theorem not_isNontrivialLogicalOperator_of_harmless
    (hS : S.toSubgroup = Subgroup.closure (listToSet L)) {g : NQubitPauliGroupElement n}
    (h : Harmless L g.operators) : ¬IsNontrivialLogicalOperator g S := by
  rintro ⟨h_cent, h_ne⟩
  rw [mem_centralizer_iff_closure g S (listToSet L) hS] at h_cent
  rcases h with ⟨s, hs, h_anti⟩ | h_span
  · have h0 := (commutes_iff_symplectic_inner_zero s g).mp (h_cent s hs)
    rw [symplecticInner_comm] at h0
    exact absurd (h0.symm.trans h_anti) (by decide)
  · obtain ⟨s, hs, hs_eq⟩ :=
      exists_mem_closure_of_symp_in_span L g.operators ((inSpan_iff L _).mp h_span)
    exact h_ne s (hS ▸ hs) hs_eq

/-- A logical witness is a nontrivial logical operator. Commuting with `L` puts
it in the centralizer, and lying outside the span means no stabilizer shares its
operator part. -/
theorem isNontrivialLogicalOperator_of_isLogicalWitness
    (hS : S.toSubgroup = Subgroup.closure (listToSet L)) {d : ℕ}
    {g : NQubitPauliGroupElement n} (h : IsLogicalWitness L d g) :
    IsNontrivialLogicalOperator g S := by
  obtain ⟨-, h_comm, h_span⟩ := h
  refine ⟨(mem_centralizer_iff_closure g S (listToSet L) hS).mpr fun s hs => ?_,
    fun s hs hs_eq => h_span ((inSpan_iff L _).mpr ?_)⟩
  · rw [commutes_iff_symplectic_inner_zero, symplecticInner_comm]
    exact h_comm s hs
  · rw [← hs_eq]
    exact mem_closure_implies_symp_in_span L s (hS ▸ hs)

/-- **Distance from decided checks.** If `g` is a logical witness of weight `d`
and every operator of weight `1, …, d − 1` is harmless, the stabilizer group
generated by `L` has distance `d`. -/
theorem hasCodeDistance_of_decide (C : StabilizerCode n k)
    (hS : C.toStabilizerGroup.toSubgroup = Subgroup.closure (listToSet L)) {d : ℕ}
    (g : NQubitPauliGroupElement n) (hg : IsLogicalWitness L d g)
    (hlow : NoLogicalBelow L d) : HasCodeDistance C d := by
  have hg' := isNontrivialLogicalOperator_of_isLogicalWitness hS hg
  have hd : 1 ≤ d := hg.1 ▸ hg'.weight_pos
  refine hasCodeDistance_of C d hd ⟨g, hg', hg.1⟩ fun w hw1 hwd g' hg'w => ?_
  refine not_isNontrivialLogicalOperator_of_harmless hS (hlow w ?_ _ ?_)
  · rw [List.mem_range'_1]
    omega
  · rw [← hg'w]
    exact mem_ofWeight _

end Soundness

/-- **Distance of a presented code from decided checks.** For a literal
presentation both hypotheses are closed propositions:

```lean
presentation.hasCodeDistance_of_decide σ[IYYIX] (by decide +kernel) (by decide +kernel)
```
-/
theorem StabilizerCode.Presentation.hasCodeDistance_of_decide
    (P : StabilizerCode.Presentation n k) {d : ℕ} (g : NQubitPauliGroupElement n)
    (hg : IsLogicalWitness P.generatorsList d g) (hlow : NoLogicalBelow P.generatorsList d) :
    HasCodeDistance P.toCode d :=
  StabilizerGroup.hasCodeDistance_of_decide P.toCode P.toCode_toSubgroup g hg hlow

end StabilizerGroup

end Quantum
