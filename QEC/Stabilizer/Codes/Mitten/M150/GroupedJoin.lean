import QEC.Stabilizer.Codes.Mitten.M150.FloorCore

namespace Quantum.Stabilizer.Homological.LP.M150

/-- Two lists of classified triples with the same shared-block mask. -/
structure JoinBucket where
  key : Nat
  left : List Nat
  right : List Nat
  deriving DecidableEq

/-- Flatten the first census in shared-block order. -/
def joinLeft (buckets : List JoinBucket) : List Nat :=
  buckets.flatMap JoinBucket.left

/-- Flatten the second census in shared-block order. -/
def joinRight (buckets : List JoinBucket) : List Nat :=
  buckets.flatMap JoinBucket.right

/-- Verify ordered keys, their entries, and only compatible pairs. -/
def checkJoinBuckets (rows : List Nat) : Nat → List JoinBucket → Bool
  | _, [] => true
  | lower, b :: bs =>
      Nat.ble lower b.key &&
      b.left.all (fun pk => Nat.beq (Nat.shiftRight pk 60) b.key) &&
      b.right.all (fun pk => Nat.beq (Nat.shiftRight pk 60) b.key) &&
      checkJoin b.left b.right rows && checkJoinBuckets rows (b.key + 1) bs

/-- Accepted buckets have strictly ordered keys and valid local joins. -/
theorem checkJoinBuckets_sound (rows : List Nat) :
    ∀ lower buckets, checkJoinBuckets rows lower buckets = true →
      buckets.Pairwise (fun a b => a.key < b.key) ∧
      ∀ b ∈ buckets, lower ≤ b.key ∧
        (∀ pk ∈ b.left, pk >>> 60 = b.key) ∧
        (∀ pk ∈ b.right, pk >>> 60 = b.key) ∧
        checkJoin b.left b.right rows = true := by
  intro lower buckets
  induction buckets generalizing lower with
  | nil => simp
  | cons b bs ih =>
    intro h
    simp only [checkJoinBuckets, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨hlo, hl⟩, hr⟩, hj⟩, ht⟩ := h
    obtain ⟨hs, hm⟩ := ih (b.key + 1) ht
    refine ⟨List.pairwise_cons.mpr ⟨?_, hs⟩, ?_⟩
    · intro c hc
      exact (hm c hc).1
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨hlo, ?_, ?_, hj⟩
        · intro pk hpk
          exact Nat.beq_eq.mp (List.all_eq_true.mp hl pk hpk)
        · intro pk hpk
          exact Nat.beq_eq.mp (List.all_eq_true.mp hr pk hpk)
      · have hh := hm c hc
        exact ⟨by omega, hh.2⟩

/-- Strictly ordered keys identify their bucket uniquely. -/
theorem joinBucket_eq_of_key_eq {buckets : List JoinBucket}
    (hs : buckets.Pairwise (fun a b => a.key < b.key))
    {a b : JoinBucket} (ha : a ∈ buckets) (hb : b ∈ buckets)
    (he : a.key = b.key) : a = b := by
  induction buckets with
  | nil => simp at ha
  | cons c cs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp ha with hca | hta
    · subst a
      rcases List.mem_cons.mp hb with hcb | htb
      · exact hcb.symm
      · have := hhead b htb
        omega
    · rcases List.mem_cons.mp hb with hcb | htb
      · subst b
        have := hhead a hta
        omega
      · exact ih htail hta htb

/-- Ordered grouped joins imply the original complete Cartesian check. -/
theorem checkJoin_of_buckets (rows : List Nat) (buckets : List JoinBucket)
    (hc : checkJoinBuckets rows 0 buckets = true) :
    checkJoin (joinLeft buckets) (joinRight buckets) rows = true := by
  obtain ⟨hs, hm⟩ := checkJoinBuckets_sound rows 0 buckets hc
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨pa, hpa, rfl⟩ := List.mem_map.mp ha
  apply List.all_eq_true.mpr
  intro b hb
  obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hb
  obtain ⟨ba, hba, hpa⟩ := List.mem_flatMap.mp hpa
  obtain ⟨bb, hbb, hpb⟩ := List.mem_flatMap.mp hpb
  by_cases he : pa >>> 60 = pb >>> 60
  · have hkey : ba.key = bb.key := by
      rw [← (hm ba hba).2.1 pa hpa, ← (hm bb hbb).2.2.1 pb hpb]
      exact he
    have hsame := joinBucket_eq_of_key_eq hs hba hbb hkey
    subst bb
    exact List.all_eq_true.mp
      (List.all_eq_true.mp (hm ba hba).2.2.2 _ (List.mem_map_of_mem hpa))
      _ (List.mem_map_of_mem hpb)
  · apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    left
    exact bne_iff_ne.mpr he

end Quantum.Stabilizer.Homological.LP.M150
