import QEC.Stabilizer.Framework.Homological.Certificate.BitsetTrie

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Intersect a bitset with successive required values of binary label planes. -/
def filterPlanes : List Nat → Nat → Nat → Nat
  | [], _, a => a
  | p :: ps, t, a =>
      let z := Nat.land a p
      filterPlanes ps (Nat.shiftRight t 1)
        (if Nat.beq (Nat.land t 1) 0 then Nat.xor a z else z)

/-- A surviving bit is exactly a domain element whose label has the target value. -/
theorem filterPlanes_testBit (ps : List Nat) :
    ∀ t a i, (filterPlanes ps t a).testBit i = true ↔
      a.testBit i = true ∧ trieRel (ps.map fun p => (p, 0)) t i 0 := by
  induction ps with
  | nil => simp [filterPlanes, trieRel]
  | cons p ps ih =>
    intro t a i
    simp only [filterPlanes, ih, List.map_cons, trieRel]
    have hmod : t % 2 < 2 := Nat.mod_lt _ (by decide)
    have hz : (Nat.beq (Nat.land t 1) 0) = !(t.testBit 0) := by
      change Nat.beq (t &&& 1) 0 = _
      simp only [Nat.and_one_is_mod, Nat.testBit_zero]
      by_cases h : t % 2 = 0
      · simp [h]
      · have h1 : t % 2 = 1 := by omega
        simp [h1]
        rfl
    rw [hz]
    cases ha : a.testBit i <;> cases hp : p.testBit i <;> cases ht : t.testBit 0 <;>
      simp_all [Nat.testBit_xor, Nat.testBit_and]

/-- An exact checked output bitset contains every eligible target-labelled entry. -/
theorem filterPlanes_complete (ps : List Nat) (t domain expected i : Nat)
    (hcheck : filterPlanes ps t domain = expected)
    (hdomain : domain.testBit i = true)
    (hrel : trieRel (ps.map fun p => (p, 0)) t i 0) :
    expected.testBit i = true := by
  rw [← hcheck]
  exact (filterPlanes_testBit ps t domain i).2 ⟨hdomain, hrel⟩

#print axioms filterPlanes_complete
end Quantum.Stabilizer.Homological.F2Mask
