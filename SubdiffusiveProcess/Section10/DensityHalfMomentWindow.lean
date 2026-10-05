module

public import SubdiffusiveProcess.Section10.DensityHalfMomentAlgebra
public import SubdiffusiveProcess.Section10.ChaosNullCarrier

@[expose] public section

/-! The geometric sublevel estimate on the actual same-limit representative. -/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology Set
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem same_limit_sublevel_half_moment_bound
    (hd : 0 < d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w))
    (U : Set (SpatialCoordinates d)) (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (N : ℕ) (R : ℝ) :
    (∫⁻ w, mu0 w {x | x ∈ U ∧ fineDensity M N w x ≤ R}
      ∂(chaosSampleLaw M).toMeasure) ≤
      volume U * ENNReal.ofReal (Real.sqrt R) *
        ENNReal.ofReal (densityHalfMomentRatio M ^ (N + 1)) := by
  have hB := measurableSet_le (g := fun _ => R)
    (_root_.SubdiffusiveProcess.Paper.aux_lim_measure_retained_density_joint M N) measurable_const
  have heq := _root_.SubdiffusiveProcess.Paper.aux_lim_measure_same_limit_random_window hd M hdelta mu0 hm hl hc
    U hU hUb N {q | fineDensity M N q.1 q.2 ≤ R} hB
  erw [heq]
  have hmeas : Measurable (fun q : BilateralField d × SpatialCoordinates d =>
      ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (Real.sqrt (fineDensity M N q.1 q.2))) :=
    measurable_const.mul (Real.continuous_sqrt.measurable.comp
      (stronglyMeasurable_fineDensity_uncurry M N).measurable).ennreal_ofReal
  calc
    _ ≤ ∫⁻ w, ∫⁻ x in U, ENNReal.ofReal (Real.sqrt R) *
        ENNReal.ofReal (Real.sqrt (fineDensity M N w x))
          ∂volume ∂(chaosSampleLaw M).toMeasure := by
      apply lintegral_mono
      intro w
      have hs : MeasurableSet {x | x ∈ U ∧ fineDensity M N w x ≤ R} :=
        hU.inter (measurableSet_le (continuous_fineDensity M N w).measurable measurable_const)
      calc
        _ ≤ ∫⁻ x in {x | x ∈ U ∧ fineDensity M N w x ≤ R},
            ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (Real.sqrt (fineDensity M N w x))
              ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hs] with x hx
          exact ofReal_sublevel_le_sqrt_mul_sqrt (le_of_lt (fineDensity_pos M N w x)) hx.2
        _ ≤ _ := lintegral_mono_set (fun x hx => hx.1)
    _ = ∫⁻ x in U, ∫⁻ w, ENNReal.ofReal (Real.sqrt R) *
        ENNReal.ofReal (Real.sqrt (fineDensity M N w x))
          ∂(chaosSampleLaw M).toMeasure ∂volume :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := by
      simp_rw [lintegral_const_mul _ (measurable_sqrt_fineDensity M N _).ennreal_ofReal,
        lintegral_sqrt_fineDensity]
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      ring

end SubdiffusiveProcess.Section10
