import QEC.Stabilizer.Framework.Concatenation.Constructor

/-!
# Concatenation: independence of the concatenated generators

`concatenate` takes as a hypothesis that the check-matrix rows of the
concatenated generators are linearly independent. Deciding this directly means
enumerating all `2 ^ (n₁ * n₂ - k₂)` coefficient vectors.
`ConcatCSSData.rowsLinearIndependent_concat` derives it from two conditions on
much shorter lists:

- the inner generators together with the two inner logical operators have
  linearly independent rows;
- the outer generators have linearly independent rows.

The proof restricts symplectic vectors to one block at a time, by the linear
map `blockRestrictSymp b`. An inner generator embedded in a block restricts to
itself on that block and to `0` on the others; a promoted outer generator
restricts to a combination of the two inner logical operators; and a vector
whose restrictions all vanish is `0`.

The file also provides general facts about `rowsLinearIndependent`:
`rowsLinearIndependent_append_iff` for an appended list and
`rowsLinearIndependent_map` for a mapped list.
-/

namespace Quantum

namespace NQubitPauliGroupElement

open NQubitPauliOperator Submodule

variable {n : ℕ}

/-! ## Row independence of appended and mapped lists -/

/-- The rows of `A ++ B` are linearly independent iff the rows of `A` are, the
rows of `B` are, and the spans of the two sets of rows are disjoint. -/
theorem rowsLinearIndependent_append_iff (A B : List (NQubitPauliGroupElement n)) :
    rowsLinearIndependent (A ++ B) ↔
      rowsLinearIndependent A ∧ rowsLinearIndependent B ∧
        Disjoint (sympSpan A) (sympSpan B) := by
  let e : Fin A.length ⊕ Fin B.length ≃ Fin (A ++ B).length :=
    finSumFinEquiv.trans (finCongr List.length_append.symm)
  have key : (fun i => checkMatrix (A ++ B) i) ∘ e = Sum.elim (checkMatrix A) (checkMatrix B) := by
    funext s
    rcases s with i | j <;> funext col <;> simp [checkMatrix, e]
  rw [rowsLinearIndependent, ← linearIndependent_equiv e, key, linearIndependent_sum]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rfl

/-- The empty list has linearly independent rows. -/
lemma rowsLinearIndependent_nil :
    rowsLinearIndependent ([] : List (NQubitPauliGroupElement n)) :=
  linearIndependent_empty_type (ι := Fin 0)

/-- The rows of `L.map f` are linearly independent iff the symplectic vectors
of the elements `f g`, for `g` in `L`, are. -/
lemma rowsLinearIndependent_map {m : ℕ}
    (f : NQubitPauliGroupElement n → NQubitPauliGroupElement m)
    (L : List (NQubitPauliGroupElement n)) :
    rowsLinearIndependent (L.map f) ↔
      LinearIndependent (ZMod 2) fun i : Fin L.length => toSymplectic (f (L.get i)).operators := by
  have key : (fun i => checkMatrix (L.map f) i) ∘ finCongr (List.length_map f).symm =
      fun i : Fin L.length => toSymplectic (f (L.get i)).operators := by
    funext i col
    simp [checkMatrix]
  rw [rowsLinearIndependent, ← linearIndependent_equiv (finCongr (List.length_map f).symm), key]

/-- If the rows of `[x, z]` are linearly independent, a vanishing combination
of them has both coefficients `0`. -/
lemma eq_zero_of_rowsLinearIndependent_pair {x z : NQubitPauliGroupElement n}
    (h : rowsLinearIndependent [x, z]) {s t : ZMod 2}
    (hst : s • toSymplectic x.operators + t • toSymplectic z.operators = 0) : s = 0 ∧ t = 0 := by
  have h' := Fintype.linearIndependent_iff.mp h ![s, t]
    ((Fin.sum_univ_two fun i => ![s, t] i • checkMatrix [x, z] i).trans hst)
  exact ⟨h' 0, h' 1⟩

end NQubitPauliGroupElement

namespace Concatenation

open NQubitPauliGroupElement StabilizerGroup NQubitPauliOperator Submodule

variable {n₁ n₂ k₂ : ℕ}

/-! ## Restricting symplectic vectors to a block -/

/-- The position in a symplectic vector on `n₁ * n₂` qubits of each coordinate
of block `b`: the `X`-bit and the `Z`-bit of position `i` go to the `X`-bit and
the `Z`-bit of the physical qubit `qIdx b i`. -/
def blockEmbedIdx (b : Fin n₂) : Fin (n₁ + n₁) → Fin (n₁ * n₂ + n₁ * n₂) :=
  Fin.addCases (fun i => Fin.castAdd (n₁ * n₂) (qIdx b i))
    (fun i => Fin.natAdd (n₁ * n₂) (qIdx b i))

/-- Restriction of a symplectic vector on `n₁ * n₂` qubits to the coordinates
of block `b`, as a linear map. -/
def blockRestrictSymp (b : Fin n₂) :
    (Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2) →ₗ[ZMod 2] (Fin (n₁ + n₁) → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (blockEmbedIdx b)

@[simp] lemma blockRestrictSymp_castAdd (b : Fin n₂) (w : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2)
    (i : Fin n₁) :
    blockRestrictSymp b w (Fin.castAdd n₁ i) = w (Fin.castAdd (n₁ * n₂) (qIdx b i)) := by
  simp only [blockRestrictSymp, LinearMap.funLeft_apply, blockEmbedIdx, Fin.addCases_left]

@[simp] lemma blockRestrictSymp_natAdd (b : Fin n₂) (w : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2)
    (i : Fin n₁) :
    blockRestrictSymp b w (Fin.natAdd n₁ i) = w (Fin.natAdd (n₁ * n₂) (qIdx b i)) := by
  simp only [blockRestrictSymp, LinearMap.funLeft_apply, blockEmbedIdx, Fin.addCases_right]

/-- Restricting the symplectic vector of an operator to block `b` gives the
symplectic vector of its restriction to block `b`. -/
lemma blockRestrictSymp_toSymplectic (b : Fin n₂) (P : NQubitPauliOperator (n₁ * n₂)) :
    blockRestrictSymp b (toSymplectic P) = toSymplectic (restrictBlockOp b P) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [blockRestrictSymp_castAdd, toSymplectic_X_part, toSymplectic_X_part, restrictBlockOp_apply]
  · rw [blockRestrictSymp_natAdd, toSymplectic_Z_part, toSymplectic_Z_part, restrictBlockOp_apply]

/-- A vector whose restrictions to all blocks vanish is `0`. -/
lemma eq_zero_of_forall_blockRestrictSymp_zero (w : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2)
    (h : ∀ b : Fin n₂, blockRestrictSymp b w = 0) : w = 0 := by
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · have := congrFun (h (blockOf q)) (Fin.castAdd n₁ (posOf q))
    rwa [blockRestrictSymp_castAdd, qIdx_blockOf_posOf] at this
  · have := congrFun (h (blockOf q)) (Fin.natAdd n₁ (posOf q))
    rwa [blockRestrictSymp_natAdd, qIdx_blockOf_posOf] at this

/-- The symplectic vector of an element embedded in block `b` restricts to the
symplectic vector of the element on block `b` and to `0` on the other
blocks. -/
lemma blockRestrictSymp_embedBlock (b b' : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    blockRestrictSymp b' (toSymplectic (embedBlock b g).operators) =
      if b' = b then toSymplectic g.operators else 0 := by
  rw [embedBlock_operators, blockRestrictSymp_toSymplectic, restrictBlockOp_embedBlockOp]
  split_ifs
  exacts [rfl, toSymplectic_one_operators]

/-- The symplectic vector of the promotion of a single-qubit Pauli `P ≠ Y` is
the combination of the symplectic vectors of `Xbar` and `Zbar` with the
symplectic bits of `P` as coefficients. -/
lemma toSymplectic_promoteSingle (Xbar Zbar : NQubitPauliOperator n₁) {P : PauliOperator}
    (hP : P ≠ PauliOperator.Y) :
    toSymplectic (promoteSingle Xbar Zbar P) =
      P.toSymplecticSingle.1 • toSymplectic Xbar + P.toSymplecticSingle.2 • toSymplectic Zbar := by
  cases P
  · simpa [promoteSingle] using toSymplectic_one_operators (n := n₁)
  · simp [promoteSingle]
  · exact absurd rfl hP
  · simp [promoteSingle]

/-- The symplectic vector of a promoted outer element restricts on block `b` to
a combination of the symplectic vectors of `Xbar` and `Zbar`, provided the
factor at `b` is not `Y`. -/
lemma blockRestrictSymp_promoteE (Xbar Zbar : NQubitPauliOperator n₁) (b : Fin n₂)
    (t : NQubitPauliGroupElement n₂) (hY : t.operators b ≠ PauliOperator.Y) :
    blockRestrictSymp b (toSymplectic (promoteE Xbar Zbar t).operators) =
      (t.operators b).toSymplecticSingle.1 • toSymplectic Xbar +
        (t.operators b).toSymplecticSingle.2 • toSymplectic Zbar := by
  rw [promoteE_operators, blockRestrictSymp_toSymplectic, restrictBlockOp_promoteOp,
    toSymplectic_promoteSingle _ _ hY]

/-! ## Independence of the embedded inner generators -/

/-- Embedding a list with linearly independent rows into a block gives a list
with linearly independent rows: restriction to the block recovers the original
rows. -/
lemma rowsLinearIndependent_map_embedBlock (b : Fin n₂) (L : List (NQubitPauliGroupElement n₁))
    (hL : rowsLinearIndependent L) : rowsLinearIndependent (L.map (embedBlock b)) := by
  refine (rowsLinearIndependent_map _ L).mpr (LinearIndependent.of_comp (blockRestrictSymp b) ?_)
  have h : ⇑(blockRestrictSymp b) ∘
        (fun i : Fin L.length => toSymplectic (embedBlock b (L.get i)).operators) =
      fun i => checkMatrix L i :=
    funext fun i => (blockRestrictSymp_embedBlock b b (L.get i)).trans (if_pos rfl)
  rw [h]
  exact hL

/-- The span of the rows of a list of elements embedded in blocks other than
`b` restricts to `0` on block `b`. -/
lemma blockRestrictSymp_eq_zero_of_mem_sympSpan (b : Fin n₂)
    (M : List (NQubitPauliGroupElement (n₁ * n₂)))
    (hM : ∀ e ∈ M, ∃ b' ≠ b, ∃ g : NQubitPauliGroupElement n₁, e = embedBlock b' g)
    {v : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2} (hv : v ∈ sympSpan M) :
    blockRestrictSymp b v = 0 := by
  rw [sympSpan_eq_span_listToSet] at hv
  refine (span_le (p := LinearMap.ker (blockRestrictSymp b))).mpr ?_ hv
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨b', hb', g, rfl⟩ := hM e he
  exact (blockRestrictSymp_embedBlock b' b g).trans (if_neg hb'.symm)

/-- Embedding a list with linearly independent rows into each of a list of
distinct blocks gives a list with linearly independent rows. -/
lemma rowsLinearIndependent_flatMap_embedBlock (L : List (NQubitPauliGroupElement n₁))
    (hL : rowsLinearIndependent L) {bs : List (Fin n₂)} (hbs : bs.Nodup) :
    rowsLinearIndependent (bs.flatMap fun b => L.map (embedBlock b)) := by
  induction bs with
  | nil => exact rowsLinearIndependent_nil
  | cons b bs ih =>
    obtain ⟨hb, hbs⟩ := List.nodup_cons.mp hbs
    rw [List.flatMap_cons, rowsLinearIndependent_append_iff]
    refine ⟨rowsLinearIndependent_map_embedBlock b L hL, ih hbs,
      disjoint_def.mpr fun v hv hv' => eq_zero_of_forall_blockRestrictSymp_zero v fun b' => ?_⟩
    by_cases hb' : b' = b
    · -- The tail lives on blocks other than `b`.
      refine blockRestrictSymp_eq_zero_of_mem_sympSpan b' _ (fun e he => ?_) hv'
      obtain ⟨b'', hb'', he⟩ := List.mem_flatMap.mp he
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp he
      exact ⟨b'', fun h => hb (hb' ▸ h ▸ hb''), g, rfl⟩
    · -- The head lives on block `b`.
      refine blockRestrictSymp_eq_zero_of_mem_sympSpan b' _ (fun e he => ?_) hv
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp he
      exact ⟨b, Ne.symm hb', g, rfl⟩

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-- The inner generators embedded in every block have linearly independent
rows if the inner generators do. -/
lemma rowsLinearIndependent_s1PerBlockList (hCin : rowsLinearIndependent D.Pin.generatorsList) :
    rowsLinearIndependent D.s1PerBlockList :=
  rowsLinearIndependent_flatMap_embedBlock D.Pin.generatorsList hCin (List.nodup_finRange n₂)

/-! ## Independence of the promoted outer generators -/

/-- The promoted outer generators have linearly independent rows if the two
inner logical operators and the outer generators do. Restricting a vanishing
combination to a block gives a vanishing combination of the two inner logical
operators, so the combination of the outer generators vanishes at every
qubit. -/
lemma rowsLinearIndependent_promotedOuterList
    (hlog : rowsLinearIndependent [D.Cin.logicalX 0, D.Cin.logicalZ 0])
    (hout : rowsLinearIndependent (D.outerZ ++ D.outerX)) :
    rowsLinearIndependent D.promotedOuterList := by
  rw [promotedOuterList, rowsLinearIndependent_map, Fintype.linearIndependent_iff]
  intro f hf
  have hY : ∀ (i : Fin (D.outerZ ++ D.outerX).length) (b : Fin n₂),
      ((D.outerZ ++ D.outerX).get i).operators b ≠ PauliOperator.Y :=
    fun i => D.outer_gen_noY (List.get_mem _ i)
  have hcoeff : ∀ b : Fin n₂,
      ∑ i, f i * (((D.outerZ ++ D.outerX).get i).operators b).toSymplecticSingle.1 = 0 ∧
        ∑ i, f i * (((D.outerZ ++ D.outerX).get i).operators b).toSymplecticSingle.2 = 0 := by
    intro b
    have h := congrArg (blockRestrictSymp b) hf
    simp only [map_sum, map_smul, map_zero, blockRestrictSymp_promoteE _ _ b _ (hY _ b),
      smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul] at h
    exact eq_zero_of_rowsLinearIndependent_pair hlog h
  refine Fintype.linearIndependent_iff.mp hout f (funext fun col => ?_)
  rw [Finset.sum_apply, Pi.zero_apply]
  refine Fin.addCases (fun b => ?_) (fun b => ?_) col
  · simpa only [Pi.smul_apply, smul_eq_mul, checkMatrix, toSymplectic_X_part] using (hcoeff b).1
  · simpa only [Pi.smul_apply, smul_eq_mul, checkMatrix, toSymplectic_Z_part] using (hcoeff b).2

/-! ## Disjointness of the two spans -/

/-- A vector in the span of the embedded inner generators restricts on each
block to a vector in the span of the inner generators. -/
lemma blockRestrictSymp_mem_sympSpan_inner (b : Fin n₂)
    {v : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2} (hv : v ∈ sympSpan D.s1PerBlockList) :
    blockRestrictSymp b v ∈ sympSpan D.Pin.generatorsList := by
  rw [sympSpan_eq_span_listToSet] at hv
  refine (span_le (p := (sympSpan D.Pin.generatorsList).comap (blockRestrictSymp b))).mpr ?_ hv
  rintro _ ⟨e, (he : e ∈ D.s1PerBlockList), rfl⟩
  obtain ⟨b', -, he⟩ := List.mem_flatMap.mp he
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  change blockRestrictSymp b (toSymplectic (embedBlock b' g).operators) ∈
    sympSpan D.Pin.generatorsList
  rw [blockRestrictSymp_embedBlock]
  split_ifs
  exacts [toSymplectic_mem_sympSpan_of_mem hg, zero_mem _]

/-- A vector in the span of the promoted outer generators restricts on each
block to a vector in the span of the two inner logical operators. -/
lemma blockRestrictSymp_mem_span_logicals (b : Fin n₂)
    {v : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2} (hv : v ∈ sympSpan D.promotedOuterList) :
    blockRestrictSymp b v ∈ sympSpan [D.Cin.logicalX 0, D.Cin.logicalZ 0] := by
  rw [sympSpan_eq_span_listToSet] at hv
  refine (span_le (p := (sympSpan [D.Cin.logicalX 0, D.Cin.logicalZ 0]).comap
    (blockRestrictSymp b))).mpr ?_ hv
  rintro _ ⟨e, (he : e ∈ D.promotedOuterList), rfl⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  change blockRestrictSymp b (toSymplectic (promoteE D.Xbar D.Zbar t).operators) ∈
    sympSpan [D.Cin.logicalX 0, D.Cin.logicalZ 0]
  rw [blockRestrictSymp_promoteE _ _ b t (D.outer_gen_noY ht b)]
  exact add_mem
    (smul_mem _ _ (toSymplectic_mem_sympSpan_of_mem (g := D.Cin.logicalX 0) (by simp)))
    (smul_mem _ _ (toSymplectic_mem_sympSpan_of_mem (g := D.Cin.logicalZ 0) (by simp)))

/-- The span of the embedded inner generators and the span of the promoted
outer generators are disjoint if the span of the inner generators and the span
of the two inner logical operators are. -/
lemma disjoint_s1_promoted
    (hdisj : Disjoint (sympSpan D.Pin.generatorsList)
      (sympSpan [D.Cin.logicalX 0, D.Cin.logicalZ 0])) :
    Disjoint (sympSpan D.s1PerBlockList) (sympSpan D.promotedOuterList) :=
  disjoint_def.mpr fun v hv hv' => eq_zero_of_forall_blockRestrictSymp_zero v fun b =>
    disjoint_def.mp hdisj _ (D.blockRestrictSymp_mem_sympSpan_inner b hv)
      (D.blockRestrictSymp_mem_span_logicals b hv')

/-! ## Independence of the concatenated generators -/

/-- The concatenated generators have linearly independent check-matrix rows,
provided the inner generators together with the two inner logical operators do
(`hin`) and the outer generators do (`hout`). -/
theorem rowsLinearIndependent_concat
    (hin : rowsLinearIndependent (D.Pin.generatorsList ++
      [D.Cin.logicalX 0, D.Cin.logicalZ 0]))
    (hout : rowsLinearIndependent (D.outerZ ++ D.outerX)) :
    rowsLinearIndependent D.concatGeneratorsList := by
  obtain ⟨hCin, hlog, hdisj⟩ := (rowsLinearIndependent_append_iff _ _).mp hin
  exact (rowsLinearIndependent_append_iff _ _).mpr
    ⟨D.rowsLinearIndependent_s1PerBlockList hCin,
      D.rowsLinearIndependent_promotedOuterList hlog hout, D.disjoint_s1_promoted hdisj⟩

/-- Under the hypotheses of `rowsLinearIndependent_concat`, no concatenated
generator is in the subgroup generated by the others. -/
theorem generatorsIndependent_concat
    (hin : rowsLinearIndependent (D.Pin.generatorsList ++
      [D.Cin.logicalX 0, D.Cin.logicalZ 0]))
    (hout : rowsLinearIndependent (D.outerZ ++ D.outerX)) :
    GeneratorsIndependent (n₁ * n₂) D.concatGeneratorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent (D.rowsLinearIndependent_concat hin hout)

end ConcatCSSData

end Concatenation

end Quantum
