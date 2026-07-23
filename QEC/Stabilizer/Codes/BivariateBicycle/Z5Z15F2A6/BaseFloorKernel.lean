/-
# A21: kernel classification for `conv a150` / `conv b150` (row-combination certificates)

The rank fact behind the weight-6 coset sweep: the kernels of
convolution-by-`A` and convolution-by-`B` on `F₂[Z₅×Z₁₅]` coincide and
equal the 16-element span `kerElt` tabulated in `BaseFloorData.lean`.
"Every kernel element is a `kerElt`" is a `2^75`-sized statement, so it
cannot be decided; instead we certify it by Gaussian elimination in
*row-combination* form: for each of the 71 pivot cells `j` the data
provides a mask `w` of check rows whose sum `y = conv P̃ w` (the
transpose pairing, evaluated by the 3-term `adj3` form) satisfies
`y j = 1` and `y = 0` at every later pivot cell.  Peeling
(`peel_kernel`) then shows a kernel chain supported on the pivot cells
is zero, and δ-normalization on the free cells finishes the
classification (`kerA_classify`/`kerB_classify`).

NOTE: the simpler no-row-op certificate of `KernelCert.lean` (each
check row hitting its pivot and no later pivot) does **not** exist for
these full-torus systems — the peel closure of every 4-cell free set
stalls at ≤ 10 of 75 cells.  The A17 experience that no-row-op orders
"always exist" is a window-with-boundary phenomenon; row combinations
are genuinely needed here (generator note,
`qec-lab:experiments/bb_lab/scripts/a21_gen_basefloor_data.py`).

Also provides the sparse convolution evaluators (`conv_a150_apply`,
`conv_b150_apply`), the particular-solution identities
`conv a150 wABf = b150` / `conv b150 wBAf = a150`, and the
point/indicator convolution lemmas consumed by the sweep soundness
argument in `BaseFloor.lean`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.BaseFloorData

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

set_option maxRecDepth 4096

/-! ## Sparse evaluation of 3-term convolutions -/

/-- A convolution by a weight-3 polynomial evaluates as a 3-term sum. -/
lemma conv_apply_three (P : G150 → ZMod 2) (s₁ s₂ s₃ : G150)
    (hP : P = fun g => if g = s₁ ∨ g = s₂ ∨ g = s₃ then 1 else 0)
    (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ s₃) (h23 : s₂ ≠ s₃)
    (v : G150 → ZMod 2) (r : G150) :
    conv P v r = v (r - s₁) + v (r - s₂) + v (r - s₃) := by
  subst hP
  simp only [conv_apply]
  have hsub : ∑ h ∈ insert s₁ (insert s₂ {s₃}),
        (if h = s₁ ∨ h = s₂ ∨ h = s₃ then (1 : ZMod 2) else 0) * v (r - h)
      = ∑ h : G150,
        (if h = s₁ ∨ h = s₂ ∨ h = s₃ then (1 : ZMod 2) else 0) * v (r - h) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro h _ hh
    have hne : ¬ (h = s₁ ∨ h = s₂ ∨ h = s₃) := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hh
    rw [if_neg hne, zero_mul]
  rw [← hsub,
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_singleton, h12, h13]),
    Finset.sum_insert (by simp [Finset.mem_singleton, h23]),
    Finset.sum_singleton]
  simp only [eq_self_iff_true, true_or, or_true, if_true, one_mul]
  ring

/-- Sparse evaluation of `conv a150` (`A = 1 + y + x`). -/
lemma conv_a150_apply (v : G150 → ZMod 2) (r : G150) :
    conv a150 v r = v (r - (0, 0)) + v (r - (0, 1)) + v (r - (1, 0)) :=
  conv_apply_three a150 (0, 0) (0, 1) (1, 0) rfl
    (by decide) (by decide) (by decide) v r

/-- Sparse evaluation of `conv b150` (`B = xy⁶ + xy¹⁰ + x²y¹²`). -/
lemma conv_b150_apply (v : G150 → ZMod 2) (r : G150) :
    conv b150 v r = v (r - (1, 6)) + v (r - (1, 10)) + v (r - (2, 12)) :=
  conv_apply_three b150 (1, 6) (1, 10) (2, 12) rfl
    (by decide) (by decide) (by decide) v r

/-! ## The adjoint pairing and the row-combination peel -/

/-- The transpose pairing of a row-combination chain `w` against the
3-term stencil `{s₁, s₂, s₃}`: `adj3 w c = (conv P̃ w) c` where `P̃` is
the reflected polynomial.  `adj3 w` is the row of the transposed system
selected by `w`. -/
def adj3 (s₁ s₂ s₃ : G150) (w : G150 → ZMod 2) (c : G150) : ZMod 2 :=
  w (c + s₁) + w (c + s₂) + w (c + s₃)

/-- Row-combination pairing swap: pairing `adj3 w` against `v` equals
pairing `w` against `conv P v`. -/
lemma sum_adj3_mul (s₁ s₂ s₃ : G150) (P : G150 → ZMod 2)
    (hP : ∀ (v : G150 → ZMod 2) (r : G150),
      conv P v r = v (r - s₁) + v (r - s₂) + v (r - s₃))
    (w v : G150 → ZMod 2) :
    (∑ c : G150, adj3 s₁ s₂ s₃ w c * v c) = ∑ r : G150, w r * conv P v r := by
  have hre : ∀ s : G150,
      (∑ r : G150, w r * v (r - s)) = ∑ c : G150, w (c + s) * v c := by
    intro s
    have hcs : ∀ c : G150, c + s - s = c := fun c => by abel
    calc (∑ r : G150, w r * v (r - s))
        = ∑ c : G150, w (c + s) * v (c + s - s) :=
          (Equiv.sum_comp (Equiv.addRight s) (fun r => w r * v (r - s))).symm
      _ = ∑ c : G150, w (c + s) * v c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hcs]
  have hL : (∑ c : G150, adj3 s₁ s₂ s₃ w c * v c)
      = (∑ c : G150, w (c + s₁) * v c) + (∑ c : G150, w (c + s₂) * v c)
        + (∑ c : G150, w (c + s₃) * v c) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [adj3]
    ring
  have hR : (∑ r : G150, w r * conv P v r)
      = (∑ r : G150, w r * v (r - s₁)) + (∑ r : G150, w r * v (r - s₂))
        + (∑ r : G150, w r * v (r - s₃)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hP v r]
    ring
  rw [hL, hR, hre s₁, hre s₂, hre s₃]

/-- Pairing any row combination against a kernel chain gives zero. -/
lemma sum_adj3_eq_zero (s₁ s₂ s₃ : G150) (P : G150 → ZMod 2)
    (hP : ∀ (v : G150 → ZMod 2) (r : G150),
      conv P v r = v (r - s₁) + v (r - s₂) + v (r - s₃))
    (w v : G150 → ZMod 2) (hv : conv P v = 0) :
    (∑ c : G150, adj3 s₁ s₂ s₃ w c * v c) = 0 := by
  rw [sum_adj3_mul s₁ s₂ s₃ P hP w v]
  refine Finset.sum_eq_zero fun r _ => ?_
  have h0 : conv P v r = 0 := by rw [hv]; rfl
  rw [h0, mul_zero]

/-- One certificate step: the row combination `w` pairs to `1` at the
pivot cell `j` and to `0` at every later pivot cell. -/
def stepOK (s₁ s₂ s₃ : G150) (j : G150) (w : ℕ) (later : List G150) : Bool :=
  decide (adj3 s₁ s₂ s₃ (maskFun w) j = 1)
    && decide (∀ j' ∈ later, adj3 s₁ s₂ s₃ (maskFun w) j' = 0)

/-- The full certificate checker (peel order: head is peeled first). -/
def pivOK (s₁ s₂ s₃ : G150) : List (G150 × ℕ) → Bool
  | [] => true
  | (j, w) :: rest =>
      stepOK s₁ s₂ s₃ j w (rest.map Prod.fst) && pivOK s₁ s₂ s₃ rest

/-- **Peel**: a kernel chain supported on the pivot cells of a valid
certificate is zero. -/
lemma peel_kernel (P : G150 → ZMod 2) (s₁ s₂ s₃ : G150)
    (hP : ∀ (v : G150 → ZMod 2) (r : G150),
      conv P v r = v (r - s₁) + v (r - s₂) + v (r - s₃)) :
    ∀ l : List (G150 × ℕ), pivOK s₁ s₂ s₃ l = true →
      ∀ v : G150 → ZMod 2, conv P v = 0 →
        (∀ g : G150, v g ≠ 0 → g ∈ l.map Prod.fst) → v = 0 := by
  intro l
  induction l with
  | nil =>
    intro _ v _ hsupp
    funext g
    change v g = 0
    by_contra hg
    exact List.not_mem_nil (hsupp g hg)
  | cons p rest ih =>
    obtain ⟨j, w⟩ := p
    intro hpiv v hker hsupp
    have hpiv' : (stepOK s₁ s₂ s₃ j w (rest.map Prod.fst)
        && pivOK s₁ s₂ s₃ rest) = true := hpiv
    rw [Bool.and_eq_true] at hpiv'
    obtain ⟨hstep, hrest⟩ := hpiv'
    simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hstep
    obtain ⟨hj1, hlater⟩ := hstep
    -- the pairing pins `v j`
    have hsum : (∑ c : G150, adj3 s₁ s₂ s₃ (maskFun w) c * v c) = 0 :=
      sum_adj3_eq_zero s₁ s₂ s₃ P hP (maskFun w) v hker
    have hsingle : (∑ c : G150, adj3 s₁ s₂ s₃ (maskFun w) c * v c)
        = adj3 s₁ s₂ s₃ (maskFun w) j * v j := by
      refine Finset.sum_eq_single j (fun c _ hcj => ?_)
        (fun h => absurd (Finset.mem_univ j) h)
      by_cases hvc : v c = 0
      · rw [hvc, mul_zero]
      · have hmem := hsupp c hvc
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h hcj
        · rw [hlater c h, zero_mul]
    have hvj : v j = 0 := by
      have h2 : adj3 s₁ s₂ s₃ (maskFun w) j * v j = 0 := by
        rw [← hsingle]
        exact hsum
      rwa [hj1, one_mul] at h2
    -- recurse on the tail
    refine ih hrest v hker fun g hg => ?_
    have hmem := hsupp g hg
    simp only [List.map_cons, List.mem_cons] at hmem
    rcases hmem with h | h
    · exact absurd hvj (h ▸ hg)
    · exact h

/-! ## Certificate discharge (finite checks over the generated tables) -/

/-- The `conv a150` certificate is valid. -/
lemma pivOKA_holds : pivOK (0, 0) (0, 1) (1, 0) pivListA = true := by
  native_decide

/-- The `conv b150` certificate is valid. -/
lemma pivOKB_holds : pivOK (1, 6) (1, 10) (2, 12) pivListB = true := by
  native_decide

/-- Coverage: every cell is an `A`-pivot cell or a free cell. -/
lemma coverA : ∀ g : G150,
    g ∈ pivListA.map Prod.fst ∨ g = fc1 ∨ g = fc2 ∨ g = fc3 ∨ g = fc4 := by
  native_decide

/-- Coverage: every cell is a `B`-pivot cell or a free cell. -/
lemma coverB : ∀ g : G150,
    g ∈ pivListB.map Prod.fst ∨ g = fc1 ∨ g = fc2 ∨ g = fc3 ∨ g = fc4 := by
  native_decide

/-- δ-normalization of the kernel span on the free cells. -/
lemma kerElt_at_fc : ∀ e1 e2 e3 e4 : ZMod 2,
    kerElt e1 e2 e3 e4 fc1 = e1 ∧ kerElt e1 e2 e3 e4 fc2 = e2
      ∧ kerElt e1 e2 e3 e4 fc3 = e3 ∧ kerElt e1 e2 e3 e4 fc4 = e4 := by
  native_decide

/-- The tabulated span lies in `ker (conv a150)` (pointwise 3-term form). -/
lemma kerElt_convA_pointwise : ∀ e1 e2 e3 e4 : ZMod 2, ∀ r : G150,
    kerElt e1 e2 e3 e4 (r - (0, 0)) + kerElt e1 e2 e3 e4 (r - (0, 1))
      + kerElt e1 e2 e3 e4 (r - (1, 0)) = 0 := by
  native_decide

/-- The tabulated span lies in `ker (conv b150)` (pointwise 3-term form). -/
lemma kerElt_convB_pointwise : ∀ e1 e2 e3 e4 : ZMod 2, ∀ r : G150,
    kerElt e1 e2 e3 e4 (r - (1, 6)) + kerElt e1 e2 e3 e4 (r - (1, 10))
      + kerElt e1 e2 e3 e4 (r - (2, 12)) = 0 := by
  native_decide

/-- `wAB` solves `A ⋆ wAB = B` (pointwise 3-term form). -/
lemma wAB_pointwise : ∀ r : G150,
    wABf (r - (0, 0)) + wABf (r - (0, 1)) + wABf (r - (1, 0)) = b150 r := by
  native_decide

/-- `wBA` solves `B ⋆ wBA = A` (pointwise 3-term form). -/
lemma wBA_pointwise : ∀ r : G150,
    wBAf (r - (1, 6)) + wBAf (r - (1, 10)) + wBAf (r - (2, 12)) = a150 r := by
  native_decide

/-- The kernel span annihilates under `conv a150`. -/
lemma conv_a150_kerElt (e1 e2 e3 e4 : ZMod 2) :
    conv a150 (kerElt e1 e2 e3 e4) = 0 := by
  funext r
  change conv a150 (kerElt e1 e2 e3 e4) r = 0
  rw [conv_a150_apply]
  exact kerElt_convA_pointwise e1 e2 e3 e4 r

/-- The kernel span annihilates under `conv b150`. -/
lemma conv_b150_kerElt (e1 e2 e3 e4 : ZMod 2) :
    conv b150 (kerElt e1 e2 e3 e4) = 0 := by
  funext r
  change conv b150 (kerElt e1 e2 e3 e4) r = 0
  rw [conv_b150_apply]
  exact kerElt_convB_pointwise e1 e2 e3 e4 r

/-- `conv a150 wABf = b150`: the particular-solution identity. -/
lemma conv_a150_wABf : conv a150 wABf = b150 := by
  funext r
  rw [conv_a150_apply]
  exact wAB_pointwise r

/-- `conv b150 wBAf = a150`: the mirror particular-solution identity. -/
lemma conv_b150_wBAf : conv b150 wBAf = a150 := by
  funext r
  rw [conv_b150_apply]
  exact wBA_pointwise r

/-! ## The kernel classifications -/

/-- **Kernel classification for `A`**: every chain annihilated by
`conv a150` is the tabulated span element with its own free-cell
coordinates. -/
theorem kerA_classify (v : G150 → ZMod 2) (hv : conv a150 v = 0) :
    v = kerElt (v fc1) (v fc2) (v fc3) (v fc4) := by
  have hfc := kerElt_at_fc (v fc1) (v fc2) (v fc3) (v fc4)
  have h0 : v + kerElt (v fc1) (v fc2) (v fc3) (v fc4) = 0 := by
    refine peel_kernel a150 (0, 0) (0, 1) (1, 0) conv_a150_apply pivListA
      pivOKA_holds _ ?_ ?_
    · rw [conv_add_right, hv, conv_a150_kerElt, add_zero]
    · intro g hg
      rcases coverA g with h | h | h | h | h
      · exact h
      · exfalso
        apply hg
        rw [h]
        change v fc1 + kerElt (v fc1) (v fc2) (v fc3) (v fc4) fc1 = 0
        rw [hfc.1]
        exact CharTwo.add_self_eq_zero _
      · exfalso
        apply hg
        rw [h]
        change v fc2 + kerElt (v fc1) (v fc2) (v fc3) (v fc4) fc2 = 0
        rw [hfc.2.1]
        exact CharTwo.add_self_eq_zero _
      · exfalso
        apply hg
        rw [h]
        change v fc3 + kerElt (v fc1) (v fc2) (v fc3) (v fc4) fc3 = 0
        rw [hfc.2.2.1]
        exact CharTwo.add_self_eq_zero _
      · exfalso
        apply hg
        rw [h]
        change v fc4 + kerElt (v fc1) (v fc2) (v fc3) (v fc4) fc4 = 0
        rw [hfc.2.2.2]
        exact CharTwo.add_self_eq_zero _
  funext g
  have hg : v g + kerElt (v fc1) (v fc2) (v fc3) (v fc4) g = 0 := by
    have := congrFun h0 g
    simpa using this
  calc v g
      = v g + (kerElt (v fc1) (v fc2) (v fc3) (v fc4) g
          + kerElt (v fc1) (v fc2) (v fc3) (v fc4) g) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (v g + kerElt (v fc1) (v fc2) (v fc3) (v fc4) g)
          + kerElt (v fc1) (v fc2) (v fc3) (v fc4) g := by ring
    _ = kerElt (v fc1) (v fc2) (v fc3) (v fc4) g := by
        rw [hg, zero_add]

/-- **Kernel classification for `B`** — the same span (the two kernels
coincide), certified against `pivListB`. -/
theorem kerB_classify (v : G150 → ZMod 2) (hv : conv b150 v = 0) :
    v = kerElt (v fc1) (v fc2) (v fc3) (v fc4) := by
  have hfc := kerElt_at_fc (v fc1) (v fc2) (v fc3) (v fc4)
  have h0 : v + kerElt (v fc1) (v fc2) (v fc3) (v fc4) = 0 := by
    refine peel_kernel b150 (1, 6) (1, 10) (2, 12) conv_b150_apply pivListB
      pivOKB_holds _ ?_ ?_
    · rw [conv_add_right, hv, conv_b150_kerElt, add_zero]
    · intro g hg
      rcases coverB g with h | h | h | h | h
      · exact h
      · exfalso
        apply hg
        rw [h]
        change v fc1 + kerElt (v fc1) (v fc2) (v fc3) (v fc4) fc1 = 0
        rw [hfc.1]
        exact CharTwo.add_self_eq_zero _
      · exfalso
        apply hg
        rw [h]
        change v fc2 + kerElt (v fc1) (v fc2) (v fc3) (v fc4) fc2 = 0
        rw [hfc.2.1]
        exact CharTwo.add_self_eq_zero _
      · exfalso
        apply hg
        rw [h]
        change v fc3 + kerElt (v fc1) (v fc2) (v fc3) (v fc4) fc3 = 0
        rw [hfc.2.2.1]
        exact CharTwo.add_self_eq_zero _
      · exfalso
        apply hg
        rw [h]
        change v fc4 + kerElt (v fc1) (v fc2) (v fc3) (v fc4) fc4 = 0
        rw [hfc.2.2.2]
        exact CharTwo.add_self_eq_zero _
  funext g
  have hg : v g + kerElt (v fc1) (v fc2) (v fc3) (v fc4) g = 0 := by
    have := congrFun h0 g
    simpa using this
  calc v g
      = v g + (kerElt (v fc1) (v fc2) (v fc3) (v fc4) g
          + kerElt (v fc1) (v fc2) (v fc3) (v fc4) g) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (v g + kerElt (v fc1) (v fc2) (v fc3) (v fc4) g)
          + kerElt (v fc1) (v fc2) (v fc3) (v fc4) g := by ring
    _ = kerElt (v fc1) (v fc2) (v fc3) (v fc4) g := by
        rw [hg, zero_add]

/-! ## Point and indicator convolutions (sweep-facing forms) -/

/-- Convolving with a point mass on the right translates. -/
lemma conv_point (w : G150 → ZMod 2) (t : G150) :
    conv w (fun g => if g = t then (1 : ZMod 2) else 0) = fun r => w (r - t) := by
  funext r
  have key : (∑ h : G150, w h * (if r - h = t then (1 : ZMod 2) else 0))
      = w (r - t) := by
    have h1 : (∑ h : G150, w h * (if r - h = t then (1 : ZMod 2) else 0))
        = w (r - t) * (if r - (r - t) = t then (1 : ZMod 2) else 0) :=
      Finset.sum_eq_single (r - t)
        (fun h _ hne => by
          have hne' : ¬ (r - h = t) := fun hc => hne (by rw [← hc]; abel)
          rw [if_neg hne', mul_zero])
        (fun h => absurd (Finset.mem_univ (r - t)) h)
    rw [h1, if_pos (show r - (r - t) = t by abel), mul_one]
  simpa [conv_apply] using key

/-- `conv` against the singleton indicator at `0` is the identity. -/
lemma conv_indicator₁ (w : G150 → ZMod 2) :
    conv w (fun g => if g = 0 then (1 : ZMod 2) else 0) = w := by
  rw [conv_point]
  funext r
  rw [sub_zero]

/-- `conv` against a two-point indicator `{0, t}`. -/
lemma conv_indicator₂ (w : G150 → ZMod 2) (t : G150) (ht : t ≠ 0) :
    conv w (fun g => if g = 0 ∨ g = t then (1 : ZMod 2) else 0)
      = fun r => w r + w (r - t) := by
  have hsplit : (fun g : G150 => if g = 0 ∨ g = t then (1 : ZMod 2) else 0)
      = (fun g : G150 => if g = 0 then (1 : ZMod 2) else 0)
        + fun g : G150 => if g = t then (1 : ZMod 2) else 0 := by
    funext g
    change _ = (if g = 0 then (1 : ZMod 2) else 0) + if g = t then 1 else 0
    by_cases h0 : g = 0
    · subst h0
      simp [Ne.symm ht]
    · by_cases htg : g = t
      · subst htg
        simp [h0]
      · simp [h0, htg]
  rw [hsplit, conv_add_right, conv_indicator₁, conv_point]
  rfl

/-- `conv` against a three-point indicator `{0, t₁, t₂}`. -/
lemma conv_indicator₃ (w : G150 → ZMod 2) (t₁ t₂ : G150)
    (h1 : t₁ ≠ 0) (h2 : t₂ ≠ 0) (h12 : t₁ ≠ t₂) :
    conv w (fun g => if g = 0 ∨ g = t₁ ∨ g = t₂ then (1 : ZMod 2) else 0)
      = fun r => w r + w (r - t₁) + w (r - t₂) := by
  have hsplit : (fun g : G150 => if g = 0 ∨ g = t₁ ∨ g = t₂ then (1 : ZMod 2) else 0)
      = (fun g : G150 => if g = 0 ∨ g = t₁ then (1 : ZMod 2) else 0)
        + fun g : G150 => if g = t₂ then (1 : ZMod 2) else 0 := by
    funext g
    change _ = (if g = 0 ∨ g = t₁ then (1 : ZMod 2) else 0) + if g = t₂ then 1 else 0
    by_cases ht2 : g = t₂
    · subst ht2
      simp [h2, Ne.symm h12]
    · by_cases h01 : g = 0 ∨ g = t₁
      · simp [h01, ht2]
      · simp [ht2, not_or.mp h01]
  rw [hsplit, conv_add_right, conv_indicator₂ w t₁ h1, conv_point]
  rfl

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
