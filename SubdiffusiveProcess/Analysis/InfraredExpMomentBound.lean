module

public import SubdiffusiveProcess.Analysis.InfraredTruncationBound
public import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment

@[expose] public section




open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- Generic transfer lemma: a nonnegative, `ν`-a.e.-strongly-measurable public-side function `Fpub`
dominated (after pulling back through `piNative`) by an integrable native-side function `Fnat` is
itself integrable on `ν := (chaosSampleLaw M).toMeasure`, with the same integral bound. Pure
measure-theoretic bookkeeping around `piNative`'s measure-preservation via `integral_map` /
`integrable_map_measure`, which need only `AEStronglyMeasurable`/`AEMeasurable`, not a
`MeasurableEmbedding`. -/
theorem integral_le_of_dominated_piNative {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Fpub : BilateralField d → ℝ) (Fnat : NativeBilateralPotentialSample d → ℝ)
    (hFpub_nonneg : ∀ beta, 0 ≤ Fpub beta)
    (hFpub_meas : AEStronglyMeasurable Fpub (chaosSampleLaw M).toMeasure)
    (hFnat_int : Integrable Fnat (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)))
    (bound : ℝ)
    (hFnat_bound : (∫ omega, Fnat omega ∂(Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))) ≤ bound)
    (hdom : ∀ᵐ omega ∂(Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)),
      Fpub (piNative omega) ≤ Fnat omega) :
    Integrable Fpub (chaosSampleLaw M).toMeasure ∧
      (∫ beta, Fpub beta ∂(chaosSampleLaw M).toMeasure) ≤ bound := by
  set μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
    with hμdef
  have hpm := piNative_measurePreserving (d := d) M
  have hcomp_meas : AEStronglyMeasurable (Fpub ∘ piNative) μ := hFpub_meas.comp_measurePreserving hpm
  have hcomp_int : Integrable (Fpub ∘ piNative) μ := by
    refine hFnat_int.mono' hcomp_meas ?_
    filter_upwards [hdom] with omega h
    show ‖Fpub (piNative omega)‖ ≤ Fnat omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hFpub_nonneg _)]
    exact h
  have hcomp_bound : (∫ omega, Fpub (piNative omega) ∂μ) ≤ bound :=
    le_trans (integral_mono_ae hcomp_int hFnat_int hdom) hFnat_bound
  have hmap_meas : AEStronglyMeasurable Fpub (Measure.map piNative μ) := by
    rw [hpm.map_eq]; exact hFpub_meas
  have hiff := integrable_map_measure hmap_meas hpm.measurable.aemeasurable
  have heq : (∫ beta, Fpub beta ∂(chaosSampleLaw M).toMeasure) = ∫ omega, Fpub (piNative omega) ∂μ := by
    rw [← hpm.map_eq]
    exact integral_map hpm.measurable.aemeasurable hmap_meas
  refine ⟨?_, ?_⟩
  · rw [← hpm.map_eq]
    exact hiff.mpr hcomp_int
  · rw [heq]; exact hcomp_bound

/-- The genuinely new half: the SAME uniform Gaussian-type exponential moment bound, but for the
finite `infraredPartialSum (·, L)` truncations of ANY characterized field (uniform in `L`), rather
than for the limit field `H` itself (which is exactly
`exists_uniform_compactExponentialMoment_of_infraredCharacterization`). No a.e.-limit-uniqueness
argument is needed here (unlike the `H` case): `infraredPartialSum (piNative omega) L` equals
`restrictForget K (positiveAnchoredInfraredTruncation omega L)` EXACTLY, for every `omega`, via
`infraredPartialSum_piNative_eq` / `restrictC_val_eq_restrictForget`. -/
theorem infraredCharacterization_truncation_exp_moment_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (K : Compacts (SpatialCoordinates d))
      (lambda : ℝ), 0 ≤ lambda → ∀ L : ℕ,
        Integrable (fun beta => Real.exp (lambda * ‖restrictC K (infraredPartialSum beta L)‖))
            (chaosSampleLaw M).toMeasure ∧
          (∫ beta, Real.exp (lambda * ‖restrictC K (infraredPartialSum beta L)‖)
              ∂(chaosSampleLaw M).toMeasure) ≤
            2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) := by
  obtain ⟨C, hCnonneg, hCM⟩ := exists_native_infrared_limit hd
  refine ⟨C, hCnonneg, ?_⟩
  intro M K lambda hlambda L
  obtain ⟨_Hn, _hHnmeas, _hHnCont, _hHnLimAE, _hLpLayer, _hLpNorm, hLpAll⟩ := hCM M
  obtain ⟨_hintH, _hboundH, _hintGrad, _hboundGrad, hLtrunc⟩ := hLpAll K lambda hlambda
  obtain ⟨hintL, hboundL, _hintGradL, _hboundGradL⟩ := hLtrunc L
  letI : MeasurableSpace C(K, ℝ) := borel _
  haveI : BorelSpace C(K, ℝ) := ⟨rfl⟩
  have hexpcont : Continuous (fun x : C(K, ℝ) => Real.exp (lambda * ‖x‖)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_norm)
  have hFpubL_meas : AEStronglyMeasurable
      (fun beta => Real.exp (lambda * ‖restrictC K (infraredPartialSum beta L)‖))
      (chaosSampleLaw M).toMeasure := by
    have h1 : Measurable (fun beta => restrictC K (infraredPartialSum beta L)) :=
      (restrictC_continuous K).measurable.comp (continuous_infraredPartialSum L).measurable
    exact (hexpcont.measurable.comp h1).aestronglyMeasurable
  have hdomL : ∀ᵐ omega ∂(Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)),
      Real.exp (lambda * ‖restrictC K (infraredPartialSum (piNative omega) L)‖) ≤
        Real.exp (lambda * compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L)) :=
    Filter.Eventually.of_forall (fun omega => by
      rw [infraredPartialSum_piNative_eq, restrictC_val_eq_restrictForget]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (norm_restrictForget_le K (positiveAnchoredInfraredTruncation omega L)) hlambda))
  exact integral_le_of_dominated_piNative M
    (fun beta => Real.exp (lambda * ‖restrictC K (infraredPartialSum beta L)‖))
    (fun omega => Real.exp (lambda * compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L)))
    (fun _ => (Real.exp_pos _).le) hFpubL_meas hintL _ hboundL hdomL



theorem infraredCharacterization_exp_moment_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ K : Compacts (SpatialCoordinates d), ∀ lambda : ℝ, 0 ≤ lambda →
        (Integrable (fun beta => Real.exp (lambda * ‖restrictC K (H beta)‖))
            (chaosSampleLaw M).toMeasure ∧
          (∫ beta, Real.exp (lambda * ‖restrictC K (H beta)‖) ∂(chaosSampleLaw M).toMeasure) ≤
            2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2)) ∧
        ∀ L : ℕ,
          Integrable (fun beta => Real.exp (lambda * ‖restrictC K (infraredPartialSum beta L)‖))
              (chaosSampleLaw M).toMeasure ∧
            (∫ beta, Real.exp (lambda * ‖restrictC K (infraredPartialSum beta L)‖)
                ∂(chaosSampleLaw M).toMeasure) ≤
              2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) := by
  obtain ⟨C1, hC1nonneg, hC1⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  obtain ⟨C2, hC2nonneg, hC2⟩ := infraredCharacterization_truncation_exp_moment_bound hd
  refine ⟨fun K => max (C1 K) (C2 K), fun K => le_trans (hC1nonneg K) (le_max_left _ _), ?_⟩
  intro M H hH K lambda hlambda
  have hbound_mono : ∀ c : ℝ, c ≤ max (C1 K) (C2 K) →
      2 * Real.exp (c * lambda ^ 2 * M.delta ^ 2) ≤
        2 * Real.exp (max (C1 K) (C2 K) * lambda ^ 2 * M.delta ^ 2) := by
    intro c hc
    gcongr
  have hH1 := hC1 M H hH K lambda hlambda
  refine ⟨⟨hH1.1, hH1.2.trans (hbound_mono (C1 K) (le_max_left _ _))⟩, ?_⟩
  intro L
  have hH2 := hC2 M K lambda hlambda L
  exact ⟨hH2.1, hH2.2.trans (hbound_mono (C2 K) (le_max_right _ _))⟩

end SubdiffusiveProcess
