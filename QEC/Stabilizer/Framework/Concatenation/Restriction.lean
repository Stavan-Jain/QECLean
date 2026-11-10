import QEC.Stabilizer.Framework.Concatenation.Embedding

/-!
# Concatenation: block restriction and blockwise commutation

`restrictBlockOp b P` reads off block `b` of an operator `P` on `n₁ * n₂`
qubits, and `restrictBlock b g` is the Pauli group element of phase `+1` with
that operator part. Weight and commutation are both computed block by block:

- `weight_eq_sum_restrictBlock`: the weight is the sum of the weights of the
  block restrictions, and `weight_ge_of_blocks_ge` bounds it below by the
  blocks of weight at least `d`;
- `symplecticInner_eq_sum_restrictBlockOp`: the symplectic inner product is the
  sum of the symplectic inner products of the block restrictions;
- `symplecticInner_embedBlockOp_left`: pairing with an operator embedded in
  block `b` is pairing with the restriction to block `b`, whence
  `restrictBlock_commute_embed_iff`, `embedBlock_cross_commute`,
  `embedBlock_commute_iff` and `embedBlock_anticommute_iff`;
- `toSymplectic_eq_sum_embedBlockOp_restrictBlockOp`: an operator is, as a
  symplectic vector, the sum of its embedded block restrictions.
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement NQubitPauliOperator

variable {n₁ n₂ : ℕ}

/-! ## Block restriction -/

/-- The operator on `n₁` qubits read off block `b` of an operator on `n₁ * n₂`
qubits. -/
def restrictBlockOp (b : Fin n₂) (P : NQubitPauliOperator (n₁ * n₂)) : NQubitPauliOperator n₁ :=
  fun i => P (qIdx b i)

/-- The Pauli group element of phase `+1` whose operator part is block `b` of
`g`. The phase of `g` is discarded. -/
def restrictBlock (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    NQubitPauliGroupElement n₁ :=
  ofOperator (restrictBlockOp b g.operators)

@[simp] lemma restrictBlockOp_apply (b : Fin n₂) (P : NQubitPauliOperator (n₁ * n₂))
    (i : Fin n₁) : restrictBlockOp b P i = P (qIdx b i) := rfl

@[simp] lemma restrictBlock_phasePower (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (restrictBlock b g).phasePower = 0 := rfl

@[simp] lemma restrictBlock_operators (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (restrictBlock b g).operators = restrictBlockOp b g.operators := rfl

/-- Up to phase, restriction to a block is multiplicative. -/
lemma restrictBlock_mul_operators (b : Fin n₂) (x y : NQubitPauliGroupElement (n₁ * n₂)) :
    (restrictBlock b (x * y)).operators = (restrictBlock b x * restrictBlock b y).operators :=
  rfl

/-- An operator embedded in block `b` restricts to itself on block `b` and to
the identity on the other blocks. -/
lemma restrictBlockOp_embedBlockOp (b b' : Fin n₂) (P : NQubitPauliOperator n₁) :
    restrictBlockOp b' (embedBlockOp b P) = if b' = b then P else identity n₁ := by
  funext i
  by_cases h : b' = b <;> simp [embedBlockOp, h, identity]

/-- Embedding the restriction to block `b` keeps block `b` and replaces the
other blocks by the identity. -/
lemma embedBlockOp_restrictBlockOp_apply (b : Fin n₂) (P : NQubitPauliOperator (n₁ * n₂))
    (q : Fin (n₁ * n₂)) :
    embedBlockOp b (restrictBlockOp b P) q = if blockOf q = b then P q else PauliOperator.I := by
  by_cases h : blockOf q = b
  · subst h
    simp [embedBlockOp]
  · simp [embedBlockOp, h]

/-! ## Weight -/

/-- The weight of an element on `n₁ * n₂` qubits is the sum of the weights of
its block restrictions. -/
theorem weight_eq_sum_restrictBlock (g : NQubitPauliGroupElement (n₁ * n₂)) :
    g.weight = ∑ b, (restrictBlock b g).weight := by
  simp only [NQubitPauliGroupElement.weight, NQubitPauliOperator.weight,
    NQubitPauliOperator.support, Finset.card_filter]
  exact sum_eq_sum_blocks _

/-- Embedding into a block preserves the weight. -/
@[simp] lemma weight_embedBlock (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    (embedBlock b g).weight = g.weight := by
  rw [weight_eq_sum_restrictBlock, Fintype.sum_eq_single b fun b' hb' => by
    simp [NQubitPauliGroupElement.weight, restrictBlockOp_embedBlockOp, hb']]
  simp [NQubitPauliGroupElement.weight, restrictBlockOp_embedBlockOp]

/-- If the restrictions of `g` to the blocks in `B` all have weight at least
`d`, then `g` has weight at least `d * |B|`. -/
theorem weight_ge_of_blocks_ge (d : ℕ) (g : NQubitPauliGroupElement (n₁ * n₂))
    (B : Finset (Fin n₂)) (hB : ∀ b ∈ B, d ≤ (restrictBlock b g).weight) :
    d * B.card ≤ g.weight := by
  rw [weight_eq_sum_restrictBlock, mul_comm, ← smul_eq_mul]
  exact (Finset.card_nsmul_le_sum B _ d hB).trans
    (Finset.sum_le_sum_of_subset (Finset.subset_univ B))

/-! ## The symplectic inner product, block by block -/

/-- The symplectic inner product of two operators on `n₁ * n₂` qubits is the
sum of the symplectic inner products of their block restrictions. -/
theorem symplecticInner_eq_sum_restrictBlockOp (P Q : NQubitPauliOperator (n₁ * n₂)) :
    symplecticInner P Q = ∑ b, symplecticInner (restrictBlockOp b P) (restrictBlockOp b Q) :=
  sum_eq_sum_blocks _

/-- Pairing an operator embedded in block `b` with `Q` is pairing it with the
restriction of `Q` to block `b`. -/
lemma symplecticInner_embedBlockOp_left (b : Fin n₂) (P : NQubitPauliOperator n₁)
    (Q : NQubitPauliOperator (n₁ * n₂)) :
    symplecticInner (embedBlockOp b P) Q = symplecticInner P (restrictBlockOp b Q) := by
  rw [symplecticInner_eq_sum_restrictBlockOp, Fintype.sum_eq_single b fun b' hb' => by
    rw [restrictBlockOp_embedBlockOp, if_neg hb', symplecticInner_identity_left],
    restrictBlockOp_embedBlockOp, if_pos rfl]

/-- Pairing `P` with an operator embedded in block `b` is pairing the
restriction of `P` to block `b` with it. -/
lemma symplecticInner_embedBlockOp_right (b : Fin n₂) (P : NQubitPauliOperator (n₁ * n₂))
    (Q : NQubitPauliOperator n₁) :
    symplecticInner P (embedBlockOp b Q) = symplecticInner (restrictBlockOp b P) Q := by
  rw [symplecticInner_comm, symplecticInner_embedBlockOp_left, symplecticInner_comm]

/-- Embedding two elements into the same block preserves their symplectic inner
product. -/
lemma symplecticInner_embedBlock (b : Fin n₂) (g g' : NQubitPauliGroupElement n₁) :
    ⟪embedBlock b g, embedBlock b g'⟫ₛ = ⟪g, g'⟫ₛ := by
  rw [embedBlock_operators, embedBlock_operators, symplecticInner_embedBlockOp_left,
    restrictBlockOp_embedBlockOp, if_pos rfl]

/-! ## Commutation -/

/-- An element commutes with an element embedded in block `b` iff its
restriction to block `b` commutes with the embedded element. -/
theorem restrictBlock_commute_embed_iff (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂))
    (s : NQubitPauliGroupElement n₁) :
    g * embedBlock b s = embedBlock b s * g ↔ restrictBlock b g * s = s * restrictBlock b g := by
  rw [commutes_iff_symplectic_inner_zero, commutes_iff_symplectic_inner_zero,
    embedBlock_operators, restrictBlock_operators, symplecticInner_embedBlockOp_right]

/-- Elements embedded in different blocks commute. -/
theorem embedBlock_cross_commute {b b' : Fin n₂} (hbb : b ≠ b')
    (g g' : NQubitPauliGroupElement n₁) :
    embedBlock b g * embedBlock b' g' = embedBlock b' g' * embedBlock b g := by
  rw [commutes_iff_symplectic_inner_zero, embedBlock_operators, embedBlock_operators,
    symplecticInner_embedBlockOp_left, restrictBlockOp_embedBlockOp, if_neg hbb,
    symplecticInner_identity_right]

/-- Elements embedded in the same block commute iff the original elements
do. -/
theorem embedBlock_commute_iff (b : Fin n₂) (g g' : NQubitPauliGroupElement n₁) :
    embedBlock b g * embedBlock b g' = embedBlock b g' * embedBlock b g ↔ g * g' = g' * g := by
  rw [commutes_iff_symplectic_inner_zero, commutes_iff_symplectic_inner_zero,
    symplecticInner_embedBlock]

/-- Elements embedded in the same block anticommute iff the original elements
do. -/
theorem embedBlock_anticommute_iff (b : Fin n₂) (g g' : NQubitPauliGroupElement n₁) :
    Anticommute (embedBlock b g) (embedBlock b g') ↔ Anticommute g g' := by
  rw [anticommutes_iff_symplectic_inner_one, anticommutes_iff_symplectic_inner_one,
    symplecticInner_embedBlock]

/-! ## Symplectic vectors -/

/-- The symplectic vector of an operator is the sum over the blocks of the
symplectic vectors of its embedded block restrictions. -/
lemma toSymplectic_eq_sum_embedBlockOp_restrictBlockOp (P : NQubitPauliOperator (n₁ * n₂)) :
    toSymplectic P = ∑ b, toSymplectic (embedBlockOp b (restrictBlockOp b P)) := by
  funext j
  rw [Finset.sum_apply]
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · rw [toSymplectic_X_part, Fintype.sum_eq_single (blockOf q) fun b hb => by
      rw [toSymplectic_X_part, embedBlockOp_restrictBlockOp_apply, if_neg hb.symm]
      rfl, toSymplectic_X_part, embedBlockOp_restrictBlockOp_apply, if_pos rfl]
  · rw [toSymplectic_Z_part, Fintype.sum_eq_single (blockOf q) fun b hb => by
      rw [toSymplectic_Z_part, embedBlockOp_restrictBlockOp_apply, if_neg hb.symm]
      rfl, toSymplectic_Z_part, embedBlockOp_restrictBlockOp_apply, if_pos rfl]

end Quantum.Concatenation
