import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.BottomForestGroup
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Cap1List
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.DualConstraints

noncomputable section
namespace Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
open F2Mask FiberData PackedDigits

/-- Equal-length zipped metadata supplies a partner for every original record. -/
theorem exists_mem_zip {α β : Type*} (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) (x : α) (hx : x ∈ xs) : ∃ y, (x,y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a as ih =>
    cases ys with
    | nil => simp at hlen
    | cons b bs =>
      have ht : as.length = bs.length := by simpa using hlen
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b,by simp⟩
      · obtain ⟨y,hy⟩ := ih bs ht hx
        exact ⟨y,by simp [hy]⟩

/-- Check the exact cap-one outside-support census against a record's existing seeds. -/
noncomputable def oneCoverCheck (r : Fiber) (ds : List (Nat × Nat)) : Bool :=
  if Nat.beq r.weight 20 then
    ds.all (fun p => Nat.beq (Nat.land p.2 r.beta) 0) &&
    r.seeds.all (fun s => Nat.ble (bitCountFast 12 s.off) 1) &&
    Nat.beq (scalarAllowed1 90 7 r.beta (ds.map Prod.snd)) (orList (r.seeds.map Seed.off)) &&
    Nat.beq (scalarZero1 90 7 r.beta (ds.map Prod.snd))
      (if (r.seeds.map Seed.off).contains 0 then 1 else 0)
  else true

/-- Packed exact-image data for a chunk of dual witnesses. -/
structure DualPacking where
  rep : Nat
  input : Nat
  output : Nat

/-- Check aligned cap-one metadata and all dual matrix images using cached literal packings. -/
noncomputable def oneGroupCheck (rs : List Fiber) (covers : List (List (Nat × Nat))) (p : DualPacking) : Bool :=
  Nat.beq rs.length covers.length && (rs.zip covers).all (fun rc => oneCoverCheck rc.1 rc.2) &&
  covers.flatten.all (fun d => Nat.blt d.1 (2^256) && Nat.blt d.2 (2^256)) &&
  Nat.beq (packList 256 (covers.flatten.map fun _ => 1)) p.rep &&
  Nat.beq (packList 256 (covers.flatten.map Prod.fst)) p.input &&
  Nat.beq (packList 256 (covers.flatten.map Prod.snd)) p.output &&
  Nat.beq (batchRecon p.rep p.input bottomDualColumns) p.output

/-- One checked cap-one record lists the outside support of every relevant actual solution. -/
theorem oneCover_complete (r : Fiber) (ds : List (Nat × Nat))
    (hforest : fiberCheck r = true) (hweight : r.weight = 20)
    (hcheck : oneCoverCheck r ds = true)
    (himages : ∀ d ∈ ds, reconX bottomDualColumns d.1 = d.2)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 1) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  simp only [oneCoverCheck,hweight,Nat.reduceBEq,if_true,Bool.and_eq_true,
    Nat.beq_eq,Nat.ble_eq,List.all_eq_true,and_assoc] at hcheck
  apply cap1_list_complete 90 7 r.beta (outsideMask word r.beta) (ds.map Prod.snd)
    (r.seeds.map Seed.off) (by decide) (outsideMask_lt _ _ _ hw) hoff (outsideMask_disjoint _ _)
  · intro z hz
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hz
    have hconstraint := bottomDual_constraint d.1 r.beta word hw
      (by rw [himages d hd];exact hcheck.1 d hd) he
    simpa only [himages d hd] using hconstraint
  · intro x hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
    have hs' := fiberCheck_seed r hforest s hs
    have hb : s.off < 2^90 := by
      rw [← hs'.2.1]
      exact outsideMask_lt _ _ _ hs'.1
    refine ⟨hb,?_⟩
    have hc := hcheck.2.1 s hs
    rw [bitCountFast_eq] at hc
    have ht := bitCount_extend 90 6 s.off hb
    change bitCount 96 s.off = bitCount 90 s.off at ht
    rw [ht] at hc
    exact hc
  · exact hcheck.2.2.1
  · exact hcheck.2.2.2

/-- Aligned cap-one chunk metadata proves outside-support coverage for every cap-one record. -/
theorem oneGroup_complete (rs : List Fiber) (covers : List (List (Nat × Nat))) (p : DualPacking)
    (hforest : groupCheck rs = true) (hcheck : oneGroupCheck rs covers p = true)
    (r : Fiber) (hr : r ∈ rs) (hweight : r.weight = 20)
    (word : Nat) (hw : word < 2^90)
    (he : reconX bottomEColumns word = reconX bottomRColumns r.beta)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 1) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  simp only [oneGroupCheck,Bool.and_eq_true,Nat.beq_eq,Nat.blt_eq,List.all_eq_true,and_assoc] at hcheck
  rcases hcheck with ⟨hlen,hcases,hbounds,hrep,hinput,houtput,hmap⟩
  have himages := reconstruction_list_sound 256 covers.flatten (by decide) hbounds
    bottomDualColumns bottomDualColumns_bounded (by rw [hrep,hinput,houtput];exact hmap)
  obtain ⟨ds,hds⟩ := exists_mem_zip rs covers hlen r hr
  apply oneCover_complete r ds (groupCheck_member rs hforest r hr) hweight (hcases _ hds)
  · intro d hd
    exact himages d (List.mem_flatten.mpr ⟨ds,(List.of_mem_zip hds).2,hd⟩)
  · exact hw
  · exact he
  · exact hoff

/-- A cap-zero outside budget selects the checked empty seed support. -/
theorem zeroGroup_complete (rs : List Fiber)
    (hcheck : (rs.all fun r => if Nat.beq r.weight 22 then
      (r.seeds.map Seed.off).contains 0 else true) = true)
    (r : Fiber) (hr : r ∈ rs) (hweight : r.weight = 22)
    (word : Nat) (hw : word < 2^90)
    (hoff : bitCount 90 (outsideMask word r.beta) ≤ 0) :
    outsideMask word r.beta ∈ r.seeds.map Seed.off := by
  have hz := mask_zero_of_bitCount_zero 90 (outsideMask word r.beta)
    (outsideMask_lt _ _ _ hw) hoff
  rw [hz]
  have h := (List.all_eq_true.mp hcheck) r hr
  simpa [hweight] using h

#print axioms oneGroup_complete
end Quantum.Stabilizer.Homological.BB.Bravyi360.BottomForest
