import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv

/-!
# Generator lists indexed by a square grid

Lattice codes list their generators by mapping a function over all coordinate
pairs `(List.finRange L).product (List.finRange L)`. This file shows that this
list contains every pair (`mem_finRange_product`), so the set of elements of
the mapped list is the range of the function
(`listToSet_map_product_finRange_eq_range`).
-/

namespace Quantum
namespace StabilizerGroup
namespace GeneratorListLemmas

open NQubitPauliGroupElement

/-- Every coordinate pair belongs to
`(List.finRange L).product (List.finRange L)`. -/
lemma mem_finRange_product (L : ℕ) (p : Fin L × Fin L) :
    p ∈ (List.finRange L).product (List.finRange L) :=
  List.mem_product.mpr ⟨List.mem_finRange p.1, List.mem_finRange p.2⟩

/-- The set of elements of the list obtained by mapping `f` over all coordinate
pairs of an `L × L` grid is the range of `f`. -/
lemma listToSet_map_product_finRange_eq_range {n L : ℕ}
    (f : Fin L × Fin L → NQubitPauliGroupElement n) :
    NQubitPauliGroupElement.listToSet
        (((List.finRange L).product (List.finRange L)).map f) =
      Set.range f :=
  Set.ext fun _ => ⟨fun hg => let ⟨a, _, h⟩ := List.mem_map.mp hg; ⟨a, h⟩,
    fun ⟨a, h⟩ => List.mem_map.mpr ⟨a, mem_finRange_product L a, h⟩⟩

end GeneratorListLemmas
end StabilizerGroup
end Quantum
