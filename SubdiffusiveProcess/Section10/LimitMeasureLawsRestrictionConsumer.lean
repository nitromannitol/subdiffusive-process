import SubdiffusiveProcess.Section10.LimitMeasureLawsRestrictionIndependence
import SubdiffusiveProcess.Section10.DensityHalfMomentConsumer




open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Concrete consumer on the existing density-divergence witness: retain its
singularity, mean, nondeterminism and weighted conclusions, and supply the
exact stationarity and all-Borel restriction-independence clauses. -/
theorem exists_density_divergence_limit_with_spatial_laws {d : ℕ}
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
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, mu0 w = m) ∧
      (∀ y : SpatialCoordinates d,
        (chaosSampleLaw M).toMeasure.map (fun w => (mu0 w).map (fun z => z + y)) =
          (chaosSampleLaw M).toMeasure.map mu0) ∧
      (∀ A B : Set (SpatialCoordinates d), MeasurableSet A → MeasurableSet B →
        (∃ c : ℝ, (d : ℝ) < c ∧ ∀ a ∈ A, ∀ b ∈ B, c ≤ ∑ i, (a i - b i) ^ 2) →
        Indep (MeasurableSpace.comap (fun w => (mu0 w).restrict A) inferInstance)
          (MeasurableSpace.comap (fun w => (mu0 w).restrict B) inferInstance)
          (chaosSampleLaw M).toMeasure) := by
  obtain ⟨mu0, hm, hl, hwl, hprops, hmean, hnd⟩ :=
    exists_same_limit_with_density_divergence hd M hdelta H
  obtain ⟨nu, hnu, hnul, hnuc⟩ := Paper.aux_lim_measure_exists_unweighted_vague_limit M
  have heq : nu =ᵐ[(chaosSampleLaw M).toMeasure] mu0 := by
    filter_upwards [hnuc, hprops] with w hvc hmc
    letI : IsLocallyFiniteMeasure (nu w) := hnul w
    letI : IsLocallyFiniteMeasure (mu0 w) := hl w
    exact Paper.aux_lim_measure_vague_unique _ _ _ hvc hmc.1
  obtain ⟨hs, hi⟩ := same_limit_stationary_and_independent M nu hnu (ae_of_all _ hnul) hnuc
  refine ⟨mu0, hm, hl, hwl, hprops, hmean, hnd, ?_, ?_⟩
  · intro y
    calc
      (chaosSampleLaw M).toMeasure.map (fun w => (mu0 w).map (fun z => z + y)) =
          (chaosSampleLaw M).toMeasure.map (fun w => (nu w).map (fun z => z + y)) :=
        Measure.map_congr (heq.symm.fun_comp (fun mu => mu.map (fun z => z + y)))
      _ = (chaosSampleLaw M).toMeasure.map nu := hs y
      _ = (chaosSampleLaw M).toMeasure.map mu0 := Measure.map_congr heq
  · intro A B hA hB hsep
    have hni : IndepFun (fun w => (nu w).restrict A) (fun w => (nu w).restrict B)
        (chaosSampleLaw M).toMeasure := (IndepFun_iff_Indep _ _ _).mpr (hi A B hA hB hsep)
    exact (IndepFun_iff_Indep _ _ _).mp (hni.congr
      (heq.fun_comp (fun mu => mu.restrict A)) (heq.fun_comp (fun mu => mu.restrict B)))

end SubdiffusiveProcess.Section10
