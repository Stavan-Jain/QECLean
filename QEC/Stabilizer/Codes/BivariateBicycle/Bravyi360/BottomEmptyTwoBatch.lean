import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomCap1Cover
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DualPlaneCertificate
import QEC.Stabilizer.Framework.Homological.Certificate.CapTwoFast

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomEmpty
open F2Mask FiberData PackedDigits BottomForest

/-- Actual dual images and a parity target excluding every outside pair. -/
structure TwoRecord where
  beta : Nat
  duals : List (Nat × Nat)
  target : Nat
  deriving Inhabited

/-- Check a bounded shadow and its complete empty outside-pair census. -/
noncomputable def twoRecordCheck (table rep : Nat) (r : TwoRecord) : Bool :=
  Nat.blt r.beta (2^90) &&
  decide (taggedPlaneCertificate 90 7 r.beta (r.duals.map Prod.snd) r.target) &&
  Nat.beq (filterPlanes ((r.duals.map fun d => Nat.land d.2 (2^90-1)).map
    (fastPairPlane 128 7 13 table rep)) r.target
    (fastPairDomain 128 7 13 table rep r.beta)) 0

/--
Check all small records and their actual dual images in one packed
reconstruction.
-/
noncomputable def twoBatchCheck (table rep : Nat) (rs : List TwoRecord) (p : DualPacking) : Bool :=
  let ds := (rs.map TwoRecord.duals).flatten
  rs.all (twoRecordCheck table rep) &&
  ds.all (fun d => Nat.blt d.1 (2^256) && Nat.blt d.2 (2^256)) &&
  Nat.beq (packList 256 (ds.map fun _ => 1)) p.rep &&
  Nat.beq (packList 256 (ds.map Prod.fst)) p.input &&
  Nat.beq (packList 256 (ds.map Prod.snd)) p.output &&
  Nat.beq (batchRecon p.rep p.input bottomDualColumns) p.output

/--
Valid actual dual images and an empty pair census exclude each actual small
solution.
-/
theorem twoRecord_impossible (table rep : Nat)
    (hlookup : ∀ x : Fin 128, dilationLookup (128*7) table x = dilate 128 7 x)
    (hrep : rep = packF 128 91 (fun _ => 1))
    (r : TwoRecord) (hcheck : twoRecordCheck table rep r = true)
    (himages : ∀ d ∈ r.duals, reconX bottomDualColumns d.1 = d.2)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 2) : False := by
  simp only [twoRecordCheck,Bool.and_eq_true,Nat.blt_eq,Nat.beq_eq,
    decide_eq_true_eq,and_assoc] at hcheck
  obtain ⟨hb,hdual,hfilter⟩ := hcheck
  obtain ⟨hbound,hdisjoint⟩ := outsideMask_bounded_disjoint 90 word r.beta hw
  have hlinear : ∀ row ∈ r.duals.map Prod.snd, row &&& r.beta = 0 →
      parityFold 7 (row &&& outsideMask word r.beta) = parityFold 7 ((row >>> 90) &&& r.beta) := by
    intro row hrow hann
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hrow
    have h := bottomDual_constraint d.1 r.beta word hw (by rw [himages d hd];exact hann) he
    simpa only [himages d hd] using h
  have hconstraints := taggedPlaneCertificate_constraints 90 7 r.beta (outsideMask word r.beta)
    (r.duals.map Prod.snd) r.target hbound hlinear hdual
  simp only [List.map_map,Function.comp_def] at hconstraints
  rw [fastPairFilter_eq 128 7 13 table rep (by decide) hlookup hrep] at hfilter
  exact cap_two_impossible 90 7 128 91 r.beta (outsideMask word r.beta) r.target
    (r.duals.map fun d => d.2 &&& (2^90-1)) (by decide) (by decide) (by decide) (by decide)
    hb hbound hoff hdisjoint
    (by intro p hp; obtain ⟨d,_,rfl⟩ := List.mem_map.mp hp; exact Nat.and_lt_two_pow _ (by decide))
    hconstraints hfilter

/--
Every record in a checked batch excludes all actual solutions with outside
weight at most two.
-/
theorem twoBatch_impossible (table rep : Nat)
    (hlookup : ∀ x : Fin 128, dilationLookup (128*7) table x = dilate 128 7 x)
    (hrep : rep = packF 128 91 (fun _ => 1))
    (rs : List TwoRecord) (p : DualPacking) (hcheck : twoBatchCheck table rep rs p = true)
    (r : TwoRecord) (hr : r ∈ rs) (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 2) : False := by
  simp only [twoBatchCheck,Bool.and_eq_true,Nat.beq_eq,Nat.blt_eq,List.all_eq_true,and_assoc] at hcheck
  rcases hcheck with ⟨hcases,hbounds,hrep',hinput,houtput,hmap⟩
  have himages := reconstruction_list_sound 256 (rs.map TwoRecord.duals).flatten
    (by decide) hbounds bottomDualColumns bottomDualColumns_bounded
    (by rw [hrep',hinput,houtput];exact hmap)
  exact twoRecord_impossible table rep hlookup hrep r (hcases r hr)
    (fun d hd => himages d (List.mem_flatten.mpr
      ⟨r.duals,List.mem_map.mpr ⟨r,hr,rfl⟩,hd⟩)) word hw he hoff

#print axioms twoBatch_impossible
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomEmpty
