module

public import SubdiffusiveProcess.Section10.DensityHalfMomentDivergence

@[expose] public section

/-! Measurability of the full-density-divergence environment event. -/

open MeasureTheory SubdiffusiveProcess Filter Topology Set
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

theorem measurableSet_density_diverges_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)) :
    MeasurableSet {w | ∀ᵐ x ∂mu0 w, Tendsto (fun n => fineDensity M n w x) atTop atTop} := by
  let U : ℕ → Set (SpatialCoordinates d) := fun j => Metric.ball 0 ((j : ℝ) + 1)
  let F : ℕ → BilateralField d → ℝ≥0∞ := fun j w =>
    mu0 w {x | x ∈ U j ∧ (w, x) ∉ densityDivergenceEvent M}
  have hf (j : ℕ) : Measurable (F j) := by
    have hfin (w : BilateralField d) : mu0 w (U j) ≠ ⊤ := by
      have := hl w
      exact Metric.isBounded_ball.measure_lt_top.ne
    exact _root_.SubdiffusiveProcess.Paper.aux_lim_measure_measurable_finite_window mu0 hm (U j)
      Metric.isOpen_ball.measurableSet hfin (densityDivergenceEvent M)ᶜ
      (measurableSet_densityDivergenceEvent M).compl
  have heq (w : BilateralField d) :
      (∀ᵐ x ∂mu0 w, Tendsto (fun n => fineDensity M n w x) atTop atTop) ↔
        ∀ j : ℕ, F j w = 0 := by
    rw [ae_iff]
    constructor
    · intro hw j
      exact measure_mono_null (fun x hx => hx.2) hw
    · intro hw
      apply measure_mono_null (t := ⋃ j : ℕ,
        {x | x ∈ U j ∧ (w, x) ∉ densityDivergenceEvent M})
      · intro x hx
        obtain ⟨j, hj⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
        exact Set.mem_iUnion.mpr ⟨j, lt_trans hj (by linarith), hx⟩
      · exact measure_iUnion_null hw
  have hset : MeasurableSet {w | ∀ j : ℕ, F j w = 0} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j => (hf j) (MeasurableSet.singleton 0)
  convert hset using 1
  ext w
  exact heq w

theorem weighted_density_divergence_event_eq {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) :
    {w | ∀ᵐ x ∂(mu0 w).withDensity (fun x => ENNReal.ofReal (Real.exp (H w x))),
      Tendsto (fun n => fineDensity M n w x) atTop atTop} =
    {w | ∀ᵐ x ∂mu0 w, Tendsto (fun n => fineDensity M n w x) atTop atTop} := by
  ext w
  simp only [mem_ofPred_eq]
  have hweight : Measurable (fun x => ENNReal.ofReal (Real.exp (H w x))) :=
    (Real.continuous_exp.comp (H w).continuous).measurable.ennreal_ofReal
  rw [ae_withDensity_iff hweight]
  constructor
  · intro hw
    filter_upwards [hw] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  · intro hw
    exact hw.mono fun x hx _ => hx

theorem measurableSet_weighted_density_diverges_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) :
    MeasurableSet {w | ∀ᵐ x ∂(mu0 w).withDensity (fun x => ENNReal.ofReal (Real.exp (H w x))),
      Tendsto (fun n => fineDensity M n w x) atTop atTop} := by
  rw [weighted_density_divergence_event_eq M mu0 H]
  exact measurableSet_density_diverges_ae M mu0 hm hl

end SubdiffusiveProcess.Section10
