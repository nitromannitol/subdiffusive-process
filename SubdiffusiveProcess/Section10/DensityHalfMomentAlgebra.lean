module

public import SubdiffusiveProcess.Section10.DensityHalfMomentFinite

@[expose] public section

/-! The sublevel algebra consumed by the same-limit random-window estimate. -/

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

theorem sublevel_le_sqrt_mul_sqrt {u R : ℝ} (hu : 0 ≤ u) (hR : u ≤ R) :
    u ≤ Real.sqrt R * Real.sqrt u := by
  calc
    u = Real.sqrt u * Real.sqrt u := (Real.mul_self_sqrt hu).symm
    _ ≤ Real.sqrt R * Real.sqrt u :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hR) (Real.sqrt_nonneg _)

theorem ofReal_sublevel_le_sqrt_mul_sqrt {u R : ℝ} (hu : 0 ≤ u) (hR : u ≤ R) :
    ENNReal.ofReal u ≤ ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (Real.sqrt u) := by
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg R)]
  exact ENNReal.ofReal_le_ofReal (sublevel_le_sqrt_mul_sqrt hu hR)

/-- A concrete F2 consumer on the actual density, before spatial integration. -/
theorem lintegral_fineDensity_sublevel {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (x : SpatialCoordinates d) (R : ℝ) :
    (∫⁻ w in {w | fineDensity M N w x ≤ R}, ENNReal.ofReal (fineDensity M N w x)
      ∂(chaosSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (densityHalfMomentRatio M ^ (N + 1)) := by
  have hm := (stronglyMeasurable_fineDensity_uncurry M N).measurable.comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : BilateralField d => x)))
  have hA : MeasurableSet {w | fineDensity M N w x ≤ R} :=
    measurableSet_le hm measurable_const
  calc
    _ ≤ ∫⁻ w in {w | fineDensity M N w x ≤ R},
        ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (Real.sqrt (fineDensity M N w x))
          ∂(chaosSampleLaw M).toMeasure := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with w hw
      exact ofReal_sublevel_le_sqrt_mul_sqrt (le_of_lt (fineDensity_pos M N w x)) hw
    _ ≤ ∫⁻ w, ENNReal.ofReal (Real.sqrt R) *
        ENNReal.ofReal (Real.sqrt (fineDensity M N w x)) ∂(chaosSampleLaw M).toMeasure :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      rw [lintegral_const_mul _ (measurable_sqrt_fineDensity M N x).ennreal_ofReal,
        lintegral_sqrt_fineDensity]

end SubdiffusiveProcess.Section10
