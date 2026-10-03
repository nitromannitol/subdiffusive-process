module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators Pointwise

noncomputable section

/-! ## Cube geometry -/

theorem isOpen_openCubeSet {d : ℕ} (Q : Homogenization.TriadicCube d) :
    IsOpen (Homogenization.openCubeSet Q) := by
  have hrw : Homogenization.openCubeSet Q =
      ⋂ i : Fin d,
        {x : Homogenization.Vec d |
            ((Q.index i : ℝ) - (1 / 2 : ℝ)) * Homogenization.cubeScaleFactor Q < x i} ∩
          {x : Homogenization.Vec d |
            x i < ((Q.index i : ℝ) + (1 / 2 : ℝ)) * Homogenization.cubeScaleFactor Q} := by
    ext x
    simp [Homogenization.openCubeSet, Set.mem_iInter]
  rw [hrw]
  refine isOpen_iInter_of_finite fun i ↦ IsOpen.inter ?_ ?_
  · exact isOpen_lt continuous_const (continuous_apply i)
  · exact isOpen_lt (continuous_apply i) continuous_const

theorem isOpen_cube (d : ℕ) (m : ℤ) : IsOpen (cube d m) :=
  isOpen_openCubeSet _

theorem isBounded_cube (d : ℕ) (m : ℤ) : Bornology.IsBounded (cube d m) :=
  Homogenization.isBounded_openCubeSet _

theorem isOpen_translatedCube (d : ℕ) (m : ℤ) (z : Vec d) :
    IsOpen (translatedCube d m z) := by
  unfold translatedCube
  have himg : (fun x ↦ z + x) '' cube d m = (fun x ↦ x - z) ⁻¹' cube d m := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y - z, hy, by ring_nf⟩
  rw [himg]
  exact (isOpen_cube d m).preimage (continuous_id.sub continuous_const)

theorem isBounded_translatedCube (d : ℕ) (m : ℤ) (z : Vec d) :
    Bornology.IsBounded (translatedCube d m z) := by
  unfold translatedCube
  have hrw : (fun x ↦ z + x) '' cube d m = z +ᵥ cube d m := by
    simp only [← Set.image_vadd, vadd_eq_add]
  rw [hrw]
  exact (isBounded_cube d m).vadd z

/-! ## Boundedness of the sup set -/

/-- On a bounded set, a continuous real function has a bounded image: the
closure is compact in the proper space `Vec d`. -/
theorem bddAbove_image_of_isBounded {d : ℕ} {W : Set (Vec d)}
    (hWbdd : Bornology.IsBounded W) {f : Vec d → ℝ} (hf : Continuous f) :
    BddAbove {r : ℝ | ∃ x ∈ W, r = f x} := by
  have hcl : IsCompact (closure W) := hWbdd.isCompact_closure
  have hbdd : BddAbove (f '' closure W) := hcl.bddAbove_image hf.continuousOn
  refine hbdd.mono ?_
  rintro r ⟨x, hx, rfl⟩
  exact ⟨x, subset_closure hx, rfl⟩

/-- A supremum of nonnegative values over a bounded set is nonnegative (and is
`0` when the set is empty, by the `Real.sSup` convention). -/
theorem sSup_image_nonneg_of_isBounded {d : ℕ} {W : Set (Vec d)}
    (hWbdd : Bornology.IsBounded W) {f : Vec d → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) : 0 ≤ sSup {r : ℝ | ∃ x ∈ W, r = f x} := by
  rcases Set.eq_empty_or_nonempty W with rfl | ⟨x, hx⟩
  · have hempty : {r : ℝ | ∃ x ∈ (∅ : Set (Vec d)), r = f x} = ∅ := by
      ext r; simp
    rw [hempty, Real.sSup_empty]
  · exact (hf0 x).trans
      (le_csSup (bddAbove_image_of_isBounded hWbdd hf) ⟨x, hx, rfl⟩)

/-! ## The countable dense reduction -/

/-- The supremum of a continuous function over an open set is the least upper
bound of its values on a countable dense subset. -/
theorem isLUB_sSup_image_countable {d : ℕ} {W : Set (Vec d)}
    (hWopen : IsOpen W) (hWbdd : Bornology.IsBounded W)
    {Q : Set (Vec d)} (hQdense : Dense Q)
    {f : Vec d → ℝ} (hf : Continuous f) (hWne : W.Nonempty) :
    IsLUB {a : ℝ | ∃ i : ↥(W ∩ Q), f (i : Vec d) = a}
      (sSup {r : ℝ | ∃ x ∈ W, r = f x}) := by
  have hDW : W ∩ Q ⊆ W := Set.inter_subset_left
  have hdense : W ⊆ closure (W ∩ Q) := hQdense.open_subset_closure_inter hWopen
  have hbdd : BddAbove {r : ℝ | ∃ x ∈ W, r = f x} :=
    bddAbove_image_of_isBounded hWbdd hf
  have hne : {r : ℝ | ∃ x ∈ W, r = f x}.Nonempty := by
    obtain ⟨x, hx⟩ := hWne
    exact ⟨f x, x, hx, rfl⟩
  constructor
  · rintro a ⟨i, rfl⟩
    exact le_csSup hbdd ⟨(i : Vec d), hDW i.2, rfl⟩
  · intro c hc
    refine csSup_le hne ?_
    rintro r ⟨y, hy, rfl⟩
    have hclosed : IsClosed {z : Vec d | f z ≤ c} :=
      isClosed_le hf continuous_const
    have hsub : W ∩ Q ⊆ {z : Vec d | f z ≤ c} := by
      intro w hw
      exact hc ⟨⟨w, hw⟩, rfl⟩
    have : y ∈ {z : Vec d | f z ≤ c} :=
      hclosed.closure_subset_iff.mpr hsub (hdense hy)
    exact this

/-! ## The measurability theorem -/

variable {Omega : Type*} [MeasurableSpace Omega]

/-- **Measurability of a literal cube supremum.**  For a family of continuous
functions depending measurably on the sample, the supremum over an open bounded
set is measurable. -/
theorem measurable_sSup_image_of_continuous {d : ℕ} {W : Set (Vec d)}
    (hWopen : IsOpen W) (hWbdd : Bornology.IsBounded W)
    {F : Omega → Vec d → ℝ}
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x : Vec d, Measurable fun omega ↦ F omega x) :
    Measurable fun omega ↦ sSup {r : ℝ | ∃ x ∈ W, r = F omega x} := by
  rcases Set.eq_empty_or_nonempty W with hW | hWne
  · subst hW
    have hzero : ∀ omega : Omega,
        {r : ℝ | ∃ x ∈ (∅ : Set (Vec d)), r = F omega x} = ∅ := by
      intro omega
      ext r
      simp
    simp only [hzero]
    exact measurable_const
  · obtain ⟨Q, hQcount, hQdense⟩ :=
      TopologicalSpace.exists_countable_dense (Homogenization.Vec d)
    haveI : Countable ↥(W ∩ Q) :=
      (hQcount.mono Set.inter_subset_right).to_subtype
    refine Measurable.isLUB
      (f := fun (i : ↥(W ∩ Q)) (omega : Omega) ↦ F omega (i : Vec d))
      (fun i ↦ hmeas _) ?_
    intro omega
    exact isLUB_sSup_image_countable hWopen hWbdd hQdense (hcont omega) hWne

/-- A supremum over a **countable** index family is measurable, given a
pointwise upper bound.  The companion of
`measurable_sSup_image_of_continuous` for the sups in `accumulatedError` whose
index set is already countable — the scale/centre sup over the triadic grid, and
the finite sup over block indices. -/
theorem measurable_sSup_of_countable_range {ι : Type*} [Countable ι] [Nonempty ι]
    {g : ι → Omega → ℝ} (hg : ∀ i, Measurable (g i))
    {S : Omega → Set ℝ}
    (hS : ∀ omega, S omega = {a : ℝ | ∃ i, g i omega = a})
    (hbdd : ∀ omega, BddAbove (S omega)) :
    Measurable fun omega ↦ sSup (S omega) := by
  refine Measurable.isLUB hg ?_
  intro omega
  rw [← hS omega]
  refine isLUB_csSup ?_ (hbdd omega)
  rw [hS omega]
  exact ⟨g (Classical.arbitrary ι) omega, Classical.arbitrary ι, rfl⟩

/-- A countable sum of nonnegative measurable real functions is measurable,
without a pointwise summability premise: the `NNReal`/`ENNReal` route makes the
non-summable branch agree at `0`.  `Measurable` twin of the landed
`ShellSensitivity.aemeasurable_tsum_of_nonneg`. -/
theorem measurable_tsum_of_nonneg {X : ℕ → Omega → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_nonneg : ∀ i omega, 0 ≤ X i omega) :
    Measurable (fun omega ↦ ∑' i, X i omega) := by
  have hnn :=
    (Measurable.nnreal_tsum fun i ↦ (hX_meas i).real_toNNReal).coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [NNReal.coe_tsum]
  apply tsum_congr
  intro i
  exact (Real.coe_toNNReal _ (hX_nonneg i omega)).symm

/-- The empty-index-tolerant form: when the index type is empty the set is empty
and `Real.sSup` returns `0`.  This is the form the `accumulatedError` terms need,
since their index sets can be empty for small `k`. -/
theorem measurable_sSup_of_countable_range' {ι : Type*} [Countable ι]
    {g : ι → Omega → ℝ} (hg : ∀ i, Measurable (g i))
    {S : Omega → Set ℝ}
    (hS : ∀ omega, S omega = {a : ℝ | ∃ i, g i omega = a})
    (hbdd : ∀ omega, BddAbove (S omega)) :
    Measurable fun omega ↦ sSup (S omega) := by
  by_cases hne : Nonempty ι
  · exact measurable_sSup_of_countable_range hg hS hbdd
  · rw [not_nonempty_iff] at hne
    have hempty : ∀ omega, S omega = (∅ : Set ℝ) := by
      intro omega
      rw [hS omega]
      ext a
      simp
    simp only [hempty]
    exact measurable_const

/-- `supNormOn` over an open bounded set is measurable. -/
theorem measurable_supNormOn_of_continuous {d : ℕ} {W : Set (Vec d)}
    (hWopen : IsOpen W) (hWbdd : Bornology.IsBounded W)
    {F : Omega → Vec d → ℝ}
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x : Vec d, Measurable fun omega ↦ F omega x) :
    Measurable fun omega ↦ supNormOn W (F omega) := by
  unfold supNormOn
  exact measurable_sSup_image_of_continuous hWopen hWbdd
    (fun omega ↦ (hcont omega).abs)
    (fun x ↦ continuous_abs.measurable.comp (hmeas x))

/-- `vectorSupNormOn` over an open bounded set is measurable. -/
theorem measurable_vectorSupNormOn_of_continuous {d : ℕ} {W : Set (Vec d)}
    (hWopen : IsOpen W) (hWbdd : Bornology.IsBounded W)
    {F : Omega → Vec d → Vec d}
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x : Vec d, Measurable fun omega ↦ F omega x)
    (hnormCont : Continuous (Homogenization.euclideanNorm (d := d)))
    (hnormMeas : Measurable (Homogenization.euclideanNorm (d := d))) :
    Measurable fun omega ↦ vectorSupNormOn W (F omega) := by
  unfold vectorSupNormOn
  exact measurable_sSup_image_of_continuous hWopen hWbdd
    (fun omega ↦ hnormCont.comp (hcont omega))
    (fun x ↦ hnormMeas.comp (hmeas x))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
