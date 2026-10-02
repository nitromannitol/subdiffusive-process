import SubdiffusiveProcess.Section10.DensityHalfMomentEvents




open MeasureTheory SubdiffusiveProcess Filter Topology Set
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

theorem exists_same_limit_with_density_divergence {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 0 < d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) :
    ∃ mu0 : BilateralField d → Measure (SpatialCoordinates d),
      Measurable mu0 ∧ (∀ w, IsLocallyFiniteMeasure (mu0 w)) ∧
      (∀ w, IsLocallyFiniteMeasure ((mu0 w).withDensity
        (fun x => ENNReal.ofReal (Real.exp (H w x))))) ∧
      (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
        MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w) ∧
        mu0 w ⟂ₘ volume ∧
        (∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
          Tendsto (fun n => fineDensity M n w x) atTop (𝓝 0)) ∧
        (∀ᵐ x ∂mu0 w, Tendsto (fun n => fineDensity M n w x) atTop atTop) ∧
        MeasuresConvergeLocally (fun n => weightedChaosCutoff M H n w)
          ((mu0 w).withDensity (fun x => ENNReal.ofReal (Real.exp (H w x)))) ∧
        (mu0 w).withDensity (fun x => ENNReal.ofReal (Real.exp (H w x))) ⟂ₘ volume ∧
        (∀ᵐ x ∂(mu0 w).withDensity (fun x => ENNReal.ofReal (Real.exp (H w x))),
          Tendsto (fun n => fineDensity M n w x) atTop atTop)) ∧
      (∀ D : Set (SpatialCoordinates d), MeasurableSet D →
        (∫⁻ w, mu0 w D ∂(chaosSampleLaw M).toMeasure) = volume D) ∧
      (¬ ∃ m : Measure (SpatialCoordinates d),
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, mu0 w = m) := by
  obtain ⟨mu0, hm, hl, hcs, hmean, hnd⟩ :=
    Paper.aux_lim_measure_exists_singular_vague_limit hd M hdelta
  have hc := hcs.mono fun w hw => hw.1
  have hloc (w : BilateralField d) : IsLocallyFiniteMeasure ((mu0 w).withDensity
      (fun x => ENNReal.ofReal (Real.exp (H w x)))) := by
    haveI := hl w
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (Real.continuous_exp.comp (H w).continuous)
  refine ⟨mu0, hm, hl, hloc, ?_, hmean, hnd⟩
  filter_upwards [hcs, Paper.aux_lim_measure_fineDensity_zero_ae M,
    same_limit_density_diverges hd M hdelta mu0 hm hl hc,
    same_limit_weighted_density_diverges hd M hdelta mu0 hm hl hc H] with w hw hv hud hwd
  haveI := hl w
  obtain ⟨hwc, _, hws⟩ :=
    Paper.aux_lim_measure_weighted_vague_and_singular M H w (mu0 w) hw.1 hw.2
  exact ⟨hw.1, hw.2, hv, hud, hwc, hws, hwd⟩

end SubdiffusiveProcess.Section10
