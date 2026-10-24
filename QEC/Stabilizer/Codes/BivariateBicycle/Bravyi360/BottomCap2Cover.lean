import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomCap1Cover
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DualPlaneCertificate
import QEC.Stabilizer.Framework.Homological.Certificate.CapTwoFast

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData PackedDigits

/-- Metadata for an exact outside-support pair census. -/
structure TwoCover where
  duals : List (Nat × Nat)
  target : Nat
  codes : List Nat

/--
Check one cap-two pair census against the canonical forest's existing seed
supports.
-/
noncomputable def twoCoverCheck (table rep : Nat) (r : Fiber) (cover : TwoCover) : Bool :=
  if Nat.beq r.weight 18 then
    decide (taggedPlaneCertificate 90 7 r.beta (cover.duals.map Prod.snd) cover.target) &&
    Nat.beq (filterPlanes ((cover.duals.map fun d => Nat.land d.2 (2^90-1)).map
      (fastPairPlane 128 7 13 table rep)) cover.target (fastPairDomain 128 7 13 table rep r.beta))
      (listedBits cover.codes) &&
    cover.codes.all (fun c => (r.seeds.map Seed.off).contains (pairMask 90 (c/128) (c%128)))
  else true

/--
Check aligned cap-two records and their cached packed dual matrix images.
-/
noncomputable def twoGroupCheck (table rep : Nat) (rs : List Fiber) (covers : List TwoCover) (p : DualPacking) : Bool :=
  let ds := (covers.map TwoCover.duals).flatten
  Nat.beq rs.length covers.length && (rs.zip covers).all (fun rc => twoCoverCheck table rep rc.1 rc.2) &&
  ds.all (fun d => Nat.blt d.1 (2^256) && Nat.blt d.2 (2^256)) &&
  Nat.beq (packList 256 (ds.map fun _ => 1)) p.rep &&
  Nat.beq (packList 256 (ds.map Prod.fst)) p.input &&
  Nat.beq (packList 256 (ds.map Prod.snd)) p.output &&
  Nat.beq (batchRecon p.rep p.input bottomDualColumns) p.output

/--
A checked cap-two record lists every possible outside support of an actual
solution.
-/
theorem twoCover_complete (table rep : Nat)
    (hlookup : ∀ x : Fin 128, dilationLookup (128*7) table x = dilate 128 7 x)
    (hrep : rep = packF 128 91 (fun _ => 1))
    (r : Fiber) (cover : TwoCover) (hforest : fiberCheck r = true) (hweight : r.weight = 18)
    (hcheck : twoCoverCheck table rep r cover = true)
    (himages : ∀ d ∈ cover.duals, reconX bottomDualColumns d.1 = d.2)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 2) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  simp only [twoCoverCheck,hweight,Nat.reduceBEq,if_true,Bool.and_eq_true,Nat.beq_eq,
    decide_eq_true_eq,List.all_eq_true,and_assoc] at hcheck
  obtain ⟨hcert,hfilter,hallowed⟩ := hcheck
  obtain ⟨hbound,hdisjoint⟩ := outsideMask_bounded_disjoint 90 word r.beta hw
  have hlinear : ∀ row ∈ cover.duals.map Prod.snd, row &&& r.beta = 0 →
      parityFold 7 (row &&& outsideMask word r.beta) = parityFold 7 ((row >>> 90) &&& r.beta) := by
    intro row hrow hann
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hrow
    have h := bottomDual_constraint d.1 r.beta word hw (by rw [himages d hd];exact hann) he
    simpa only [himages d hd] using h
  have hconstraints := taggedPlaneCertificate_constraints 90 7 r.beta (outsideMask word r.beta)
    (cover.duals.map Prod.snd) cover.target hbound hlinear hcert
  simp only [List.map_map,Function.comp_def] at hconstraints
  rw [fastPairFilter_eq 128 7 13 table rep (by decide) hlookup hrep] at hfilter
  apply cap_two_allowed 90 7 128 91 r.beta (outsideMask word r.beta) cover.target
    (cover.duals.map fun d => d.2 &&& (2^90-1)) cover.codes (r.seeds.map Seed.off)
    (by decide) (by decide) (by decide) (by decide) (fiberCheck_beta r hforest)
    hbound hoff hdisjoint _ hconstraints hfilter
  · intro c hc
    exact List.contains_iff_mem.mp (hallowed c hc)
  · intro p hp
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hp
    exact Nat.and_lt_two_pow _ (by decide)

/--
Checked aligned cap-two metadata covers each cap-two record in its canonical
forest chunk.
-/
theorem twoGroup_complete (table rep : Nat)
    (hlookup : ∀ x : Fin 128, dilationLookup (128*7) table x = dilate 128 7 x)
    (hrep : rep = packF 128 91 (fun _ => 1))
    (rs : List Fiber) (covers : List TwoCover) (p : DualPacking)
    (hforest : groupCheck rs = true) (hcheck : twoGroupCheck table rep rs covers p = true)
    (r : Fiber) (hr : r ∈ rs) (hweight : r.weight = 18)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 2) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  simp only [twoGroupCheck,Bool.and_eq_true,Nat.beq_eq,Nat.blt_eq,List.all_eq_true,and_assoc] at hcheck
  rcases hcheck with ⟨hlen,hcases,hbounds,hrep',hinput,houtput,hmap⟩
  have himages := reconstruction_list_sound 256 (covers.map TwoCover.duals).flatten
    (by decide) hbounds bottomDualColumns bottomDualColumns_bounded
    (by rw [hrep',hinput,houtput];exact hmap)
  obtain ⟨cover,hcover⟩ := exists_mem_zip rs covers hlen r hr
  apply twoCover_complete table rep hlookup hrep r cover (groupCheck_member rs hforest r hr)
    hweight (hcases _ hcover) _ word hw he hoff
  intro d hd
  exact himages d (List.mem_flatten.mpr ⟨cover.duals,
    List.mem_map.mpr ⟨cover,(List.of_mem_zip hcover).2,rfl⟩,hd⟩)

end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
