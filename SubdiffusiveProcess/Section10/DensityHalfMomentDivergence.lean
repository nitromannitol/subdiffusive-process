module

public import SubdiffusiveProcess.Section10.DensityHalfMomentWindow
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

@[expose] public section

/-! Tonelli and first Borel–Cantelli give full density divergence, on the same
everywhere locally finite unweighted limit and its exponential weighting. -/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology Set
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The full-sequence divergence event on the actual environment/spatial carrier. -/
def densityDivergenceEvent (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Set (BilateralField d × SpatialCoordinates d) :=
  {q | Tendsto (fun n => fineDensity M n q.1 q.2) atTop atTop}

theorem measurableSet_densityDivergenceEvent (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    MeasurableSet (densityDivergenceEvent M) :=
  measurableSet_tendsto atTop (fun n => (stronglyMeasurable_fineDensity_uncurry M n).measurable)

theorem tsum_half_moment_ne_top (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    (∑' n : ℕ, ENNReal.ofReal (densityHalfMomentRatio M ^ (n + 1))) ≠ ⊤ := by
  have hs : Summable (fun n : ℕ => densityHalfMomentRatio M ^ (n + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (densityHalfMomentRatio_pos M).le
        (densityHalfMomentRatio_lt_one M)).mul_right (densityHalfMomentRatio M)
  exact hs.tsum_ofReal_ne_top

theorem same_limit_sublevel_mass_summable_ae
    (hd : 0 < d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w))
    (U : Set (SpatialCoordinates d)) (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (R : ℝ) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      (∑' n : ℕ, mu0 w {x | x ∈ U ∧ fineDensity M n w x ≤ R}) ≠ ⊤ := by
  have hfin (w : BilateralField d) : mu0 w U ≠ ⊤ := by
    have := hl w
    exact hUb.measure_lt_top.ne
  have hf (n : ℕ) : Measurable (fun w => mu0 w {x | x ∈ U ∧ fineDensity M n w x ≤ R}) :=
    _root_.SubdiffusiveProcess.Paper.aux_lim_measure_measurable_finite_window mu0 hm U hU hfin _
      (measurableSet_le (stronglyMeasurable_fineDensity_uncurry M n).measurable measurable_const)
  have hsum : (∫⁻ w, ∑' n : ℕ, mu0 w {x | x ∈ U ∧ fineDensity M n w x ≤ R}
      ∂(chaosSampleLaw M).toMeasure) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (show volume U ≠ ⊤ from hUb.measure_lt_top.ne)
        (show ENNReal.ofReal (Real.sqrt R) ≠ ⊤ from ENNReal.ofReal_ne_top))
      (tsum_half_moment_ne_top M))
    rw [lintegral_tsum (fun n => (hf n).aemeasurable), ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n =>
      same_limit_sublevel_half_moment_bound hd M hdelta mu0 hm hl hc U hU hUb n R
  exact (ae_lt_top (Measurable.tsum hf) hsum).mono fun w hw => hw.ne

theorem same_limit_density_diverges
    (hd : 0 < d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w)) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      ∀ᵐ x ∂mu0 w, Tendsto (fun n => fineDensity M n w x) atTop atTop := by
  have hwin : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ j k : ℕ,
      (∑' n : ℕ, mu0 w {x | x ∈ Metric.ball (0 : SpatialCoordinates d) ((j : ℝ) + 1) ∧
        fineDensity M n w x ≤ (k : ℝ) + 1}) ≠ ⊤ := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro k
    exact same_limit_sublevel_mass_summable_ae hd M hdelta mu0 hm hl hc _
      Metric.isOpen_ball.measurableSet Metric.isBounded_ball ((k : ℝ) + 1)
  filter_upwards [hwin] with w hw
  have hx : ∀ᵐ x ∂mu0 w, ∀ j k : ℕ, ∀ᶠ n in atTop,
      x ∉ {x | x ∈ Metric.ball (0 : SpatialCoordinates d) ((j : ℝ) + 1) ∧
        fineDensity M n w x ≤ (k : ℝ) + 1} := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro k
    exact ae_eventually_notMem (hw j k)
  filter_upwards [hx] with x hx
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨j, hj⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
  have hxj : x ∈ Metric.ball (0 : SpatialCoordinates d) ((j : ℝ) + 1) :=
    lt_trans hj (by linarith)
  obtain ⟨k, hk⟩ := exists_nat_gt b
  filter_upwards [hx j k] with n hn
  have hlarge : (k : ℝ) + 1 < fineDensity M n w x :=
    lt_of_not_ge (fun h => hn ⟨hxj, h⟩)
  exact le_of_lt (lt_trans hk (lt_trans (by linarith : (k : ℝ) < (k : ℝ) + 1) hlarge))

theorem same_limit_weighted_density_diverges
    (hd : 0 < d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      ∀ᵐ x ∂(mu0 w).withDensity (fun x => ENNReal.ofReal (Real.exp (H w x))),
        Tendsto (fun n => fineDensity M n w x) atTop atTop := by
  filter_upwards [same_limit_density_diverges hd M hdelta mu0 hm hl hc] with w hw
  exact (withDensity_absolutelyContinuous _ _).ae_le hw

end SubdiffusiveProcess.Section10
