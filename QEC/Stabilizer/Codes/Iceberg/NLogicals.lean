import QEC.Stabilizer.Codes.Iceberg.N

/-!
# The iceberg codes `[[2m, 2m − 2, 2]]`: logical operators

A logical basis of `Iceberg.stabilizerCode m`. Logical qubit `i : Fin (2m − 2)`
lives on physical qubit `i`, and the last two physical qubits are anchors
shared by all logical qubits:
```
X̄ᵢ = X on qubits {i, 2m − 1},   Z̄ᵢ = Z on qubits {i, 2m − 2}.
```
Each operator acts on two qubits, so it commutes with both checks. `X̄ᵢ` and
`Z̄ᵢ` meet on qubit `i` only, so they anticommute; for `i ≠ j`, `X̄ᵢ` and `Z̄ⱼ`
have disjoint supports, so they commute.

For `m = 2` this is a basis of the four-qubit code different from the one in
`Small/FourQubit_4_2_2Logicals.lean`.

## Outline

- Qubits `logIdx`, `xAnchor`, `zAnchor`
- Logical operators `logicalX`, `logicalZ`
- Anticommutation `logicalX_anticommutes_logicalZ`
- Commutation between logical qubits: `logicalX_commutes_logicalX`,
  `logicalZ_commutes_logicalZ`, `logicalX_commutes_logicalZ_of_ne`
- Centralizer membership `logicalX_mem_centralizer`, `logicalZ_mem_centralizer`
- `stabilizerCodeWithLogicals : Code[[2m, 2m − 2]]ₗ`
-/

namespace Quantum
namespace StabilizerGroup
namespace Iceberg

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Logical operators -/

/-- The physical qubit `i` on which logical qubit `i` lives. -/
def logIdx (m : ℕ) (i : Fin (2 * m - 2)) : Fin (2 * m) :=
  Fin.castLE (Nat.sub_le _ _) i

/-- The X-anchor: qubit `2m − 1`, on which every `X̄ᵢ` acts. -/
def xAnchor (m : ℕ) [Fact (2 ≤ m)] : Fin (2 * m) :=
  ⟨2 * m - 1, by have := Fact.out (p := 2 ≤ m); omega⟩

/-- The Z-anchor: qubit `2m − 2`, on which every `Z̄ᵢ` acts. -/
def zAnchor (m : ℕ) [Fact (2 ≤ m)] : Fin (2 * m) :=
  ⟨2 * m - 2, by have := Fact.out (p := 2 ≤ m); omega⟩

/-- Distinct logical qubits live on distinct physical qubits. -/
lemma logIdx_injective (m : ℕ) : Function.Injective (logIdx m) :=
  Fin.castLE_injective (Nat.sub_le _ _)

lemma logIdx_ne_xAnchor (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) : logIdx m i ≠ xAnchor m :=
  Fin.ne_of_val_ne (show i.val ≠ 2 * m - 1 by have := i.isLt; omega)

lemma logIdx_ne_zAnchor (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) : logIdx m i ≠ zAnchor m :=
  Fin.ne_of_val_ne (show i.val ≠ 2 * m - 2 by have := i.isLt; omega)

lemma xAnchor_ne_zAnchor (m : ℕ) [Fact (2 ≤ m)] : xAnchor m ≠ zAnchor m :=
  Fin.ne_of_val_ne (show 2 * m - 1 ≠ 2 * m - 2 by have := Fact.out (p := 2 ≤ m); omega)

/-- Logical X for logical qubit `i`: X on qubits `i` and `2m − 1`. -/
def logicalX (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) : NQubitPauliGroupElement (2 * m) :=
  σ[2 * m | logIdx m i ↦ X, xAnchor m ↦ X]

/-- Logical Z for logical qubit `i`: Z on qubits `i` and `2m − 2`. -/
def logicalZ (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) : NQubitPauliGroupElement (2 * m) :=
  σ[2 * m | logIdx m i ↦ Z, zAnchor m ↦ Z]

/-- `X̄ᵢ` is `X` on the support `{i, 2m − 1}`. -/
lemma logicalX_eq_xOn (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    logicalX m i = xOn {logIdx m i, xAnchor m} :=
  (xOn_pair _ _).symm

/-- `Z̄ᵢ` is `Z` on the support `{i, 2m − 2}`. -/
lemma logicalZ_eq_zOn (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    logicalZ m i = zOn {logIdx m i, zAnchor m} :=
  (zOn_pair _ _).symm

/-! ## Anticommutation -/

/-- `X̄ᵢ` and `Z̄ᵢ` anticommute: they meet on qubit `i` only. -/
lemma logicalX_anticommutes_logicalZ (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    Anticommute (logicalX m i) (logicalZ m i) := by
  rw [logicalX_eq_xOn, logicalZ_eq_zOn]
  exact anticommute_xOn_pair_zOn_pair (xAnchor_ne_zAnchor m)

/-! ## Commutation between logical qubits -/

/-- Any two logical `X` operators commute: both are X-type. -/
lemma logicalX_commutes_logicalX (m : ℕ) [Fact (2 ≤ m)] (i j : Fin (2 * m - 2)) :
    logicalX m i * logicalX m j = logicalX m j * logicalX m i :=
  (logicalX_eq_xOn m i ▸ IsXTypeElement_xOn _).commute (logicalX_eq_xOn m j ▸ IsXTypeElement_xOn _)

/-- Any two logical `Z` operators commute: both are Z-type. -/
lemma logicalZ_commutes_logicalZ (m : ℕ) [Fact (2 ≤ m)] (i j : Fin (2 * m - 2)) :
    logicalZ m i * logicalZ m j = logicalZ m j * logicalZ m i :=
  (logicalZ_eq_zOn m i ▸ IsZTypeElement_zOn _).commute (logicalZ_eq_zOn m j ▸ IsZTypeElement_zOn _)

/-- `X̄ᵢ` and `Z̄ⱼ` commute for `i ≠ j`: their supports `{i, 2m − 1}` and
`{j, 2m − 2}` are disjoint. -/
lemma logicalX_commutes_logicalZ_of_ne (m : ℕ) [Fact (2 ≤ m)] {i j : Fin (2 * m - 2)}
    (hij : i ≠ j) : logicalX m i * logicalZ m j = logicalZ m j * logicalX m i := by
  rw [logicalX_eq_xOn, logicalZ_eq_zOn]
  refine commutes_xOn_zOn_of_disjoint (Finset.disjoint_iff_inter_eq_empty.2 ?_)
  simp [Finset.insert_inter_of_notMem, (logIdx_injective m).ne hij, logIdx_ne_zAnchor,
    (logIdx_ne_xAnchor m j).symm, xAnchor_ne_zAnchor]

/-! ## Centralizer membership

Each logical operator is `X` or `Z` on a pair of qubits, which commutes with
the stabilizer by `xOn_mem_centralizer` and `zOn_mem_centralizer`. -/

/-- `X̄ᵢ` commutes with every element of the stabilizer. -/
lemma logicalX_mem_centralizer (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    logicalX m i ∈ centralizer (stabilizerGroup m) :=
  logicalX_eq_xOn m i ▸ xOn_mem_centralizer m (even_card_pair (logIdx_ne_xAnchor m i))

/-- `Z̄ᵢ` commutes with every element of the stabilizer. -/
lemma logicalZ_mem_centralizer (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    logicalZ m i ∈ centralizer (stabilizerGroup m) :=
  logicalZ_eq_zOn m i ▸ zOn_mem_centralizer m (even_card_pair (logIdx_ne_zAnchor m i))

/-! ## The code with its logical basis `Code[[2m, 2m − 2]]ₗ` -/

/-- The iceberg code on `2m` qubits with its logical basis `X̄ᵢ = XᵢX₂ₘ₋₁`,
`Z̄ᵢ = ZᵢZ₂ₘ₋₂`. Operators of distinct logical qubits commute: they have the
same type, or disjoint supports. -/
noncomputable def stabilizerCodeWithLogicals (m : ℕ) [Fact (2 ≤ m)] :
    Code[[2 * m, 2 * m - 2]]ₗ where
  toStabilizerCode := stabilizerCode m
  logicalOps i := ⟨logicalX m i, logicalZ m i, logicalX_mem_centralizer m i,
    logicalZ_mem_centralizer m i, logicalX_anticommutes_logicalZ m i⟩
  logical_commute_cross ℓ ℓ' h := ⟨logicalX_commutes_logicalX m ℓ ℓ',
    logicalX_commutes_logicalZ_of_ne m h, (logicalX_commutes_logicalZ_of_ne m h.symm).symm,
    logicalZ_commutes_logicalZ m ℓ ℓ'⟩

end Iceberg
end StabilizerGroup
end Quantum
