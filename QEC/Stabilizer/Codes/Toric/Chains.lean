import Mathlib.Tactic
import QEC.Stabilizer.Geometry.CellComplexTypes

/-!
# Chains on the periodic square lattice

Indicator chains and supports for the chain groups `C0 L`, `C1 L`, `C2 L` of the
`L × L` periodic square lattice:

* `singleVtx v`, `singleEdge e`, `singleFace f`: the chain that is `1` on one
  cell and `0` elsewhere;
* `edgeSupport c` and `edgeWeight c`: the set of edges on which a 1-chain `c`
  is nonzero, and its cardinality.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

variable {L : ℕ}

/-! ## Indicator chains -/

/-- The indicator 0-chain of a vertex. -/
def singleVtx (v : VtxIdx L) : C0 L :=
  fun u => if u = v then (1 : ZMod 2) else 0

/-- The indicator 1-chain of an edge. -/
def singleEdge (e : EdgeIdx L) : C1 L :=
  fun e' => if e' = e then (1 : ZMod 2) else 0

/-- The indicator 2-chain of a face. -/
def singleFace (f : FaceIdx L) : C2 L :=
  fun f' => if f' = f then (1 : ZMod 2) else 0

@[simp] lemma singleVtx_apply_self (v : VtxIdx L) : singleVtx v v = 1 := by
  simp [singleVtx]

@[simp] lemma singleVtx_apply_ne {u v : VtxIdx L} (h : u ≠ v) : singleVtx v u = 0 := by
  simp [singleVtx, h]

@[simp] lemma singleEdge_apply_self (e : EdgeIdx L) : singleEdge e e = 1 := by
  simp [singleEdge]

@[simp] lemma singleEdge_apply_ne {e e' : EdgeIdx L} (h : e' ≠ e) : singleEdge e e' = 0 := by
  simp [singleEdge, h]

@[simp] lemma singleFace_apply_self (f : FaceIdx L) : singleFace f f = 1 := by
  simp [singleFace]

@[simp] lemma singleFace_apply_ne {f f' : FaceIdx L} (h : f' ≠ f) : singleFace f f' = 0 := by
  simp [singleFace, h]

/-! ## Support and weight of a 1-chain -/

/-- The support of a 1-chain: the edges on which it is nonzero. -/
def edgeSupport (c : C1 L) : Finset (EdgeIdx L) :=
  Finset.univ.filter (fun e => c e ≠ 0)

/-- The weight of a 1-chain: the number of edges in its support. -/
def edgeWeight (c : C1 L) : ℕ := (edgeSupport c).card

@[simp] lemma mem_edgeSupport (c : C1 L) (e : EdgeIdx L) :
    e ∈ edgeSupport c ↔ c e ≠ 0 := by
  simp [edgeSupport]

@[simp] lemma edgeSupport_singleEdge (e : EdgeIdx L) :
    edgeSupport (singleEdge e) = {e} := by
  ext e'
  simp [singleEdge]

@[simp] lemma edgeWeight_singleEdge (e : EdgeIdx L) :
    edgeWeight (singleEdge e) = 1 := by
  simp [edgeWeight]

end Lattice
end Stabilizer
end Quantum
