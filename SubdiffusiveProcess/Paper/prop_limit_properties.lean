module

public import SubdiffusiveProcess.Paper.mfd_prop_quenched_convergence
public import SubdiffusiveProcess.Paper.Support.LimitPropertiesSuppliers
public import SubdiffusiveProcess.Paper.inputs_lifetime_local_input
public import SubdiffusiveProcess.MultiplicativeChaos.SpeedBasic

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Live `mfd:prop-limit-properties`: construct the actual limiting kernel,
semigroup and speed measure from the native model. All properties hold on one
full-probability event for every start and time. No predecessor output is assumed. -/
theorem prop_limit_properties
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∃ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N)),
        in_crossing M H PN KN ∧
        aux_cutoff_lifetime_package_LocalInput M H KN ∧
        ∃ (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
          (hK : IsMarkovKernel K)
          (mu : BilateralField d → Measure (SpatialCoordinates d)),
          Measurable mu ∧
          (∀ B : Set (SpatialCoordinates d), IsCompact B →
            ∀ eps : ℝ, 0 < eps →
              Tendsto (fun N ↦ (chaosSampleLaw M).toMeasure
                {omega : BilateralField d | ∃ x ∈ B, eps ≤
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0)) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            MeasuresConvergeLocally
              (fun N ↦ cutoffSpeedMeasure M H omega N) (mu omega) ∧
            IsLocallyFiniteMeasure (mu omega) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (P omega).IsConservative ∧
            HasStrongMarkovRestart K omega ∧
            SemigroupSymmetric (P omega) (mu omega) ∧
            (∀ nu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) nu →
              IsLocallyFiniteMeasure nu → SemigroupSymmetric (P omega) nu)) := by
  classical
  obtain ⟨deltaQ, hdeltaQ, hquenched⟩ := mfd_prop_quenched_convergence hd
  have hp : (d : ℝ) < (2 * (d + 1) : ℕ) * (1 / 2 : ℝ) := by
    push_cast
    linarith
  obtain ⟨deltaMu, hdeltaMu, hchaos⟩ :=
    prop_chaos_growth hd (1 / 2) (by norm_num) (2 * (d + 1)) hp
  refine ⟨min deltaQ deltaMu, lt_min hdeltaQ hdeltaMu, ?_⟩
  intro M hM
  obtain ⟨H, hH, PN, KN, hKN, hin, hcauchy, _⟩ :=
    hquenched M (hM.trans (min_le_left _ _))
  have hinput : aux_cutoff_lifetime_package_LocalInput M H KN :=
    inputs_lifetime_local_input M H hd hH PN KN hKN hin
  obtain ⟨L, hL, hLlocal, _hLstrong⟩ :=
    aux_cutoff_lifetime_package_local M H KN hinput
  have hbounds := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL hLlocal
  have hstart := in_cutoff_start_continuity hd M H hH PN KN hKN hin hbounds
  obtain ⟨P, hP, K, hK, _hcontK, hlim, hconvP⟩ :=
    limit_kernel hd M H hH PN KN hKN hin hcauchy hstart hin.2.2
  have hconv : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps →
        Tendsto (fun N ↦ (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0) :=
    fun B hB eps heps =>
      aux_mfd_convergence_tendsto_of_prob _ _ (hconvP B hB eps heps)
  obtain ⟨mu, hmeas, hmuae, _⟩ :=
    hchaos M H hH (hM.trans (min_le_right _ _))
  have hmu : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) (mu omega) ∧
      IsLocallyFiniteMeasure (mu omega) := by
    filter_upwards [hmuae] with omega h
    simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using ⟨h.1, h.2.1⟩
  have hprops := aux_prop_limit_properties_of_suppliers hd M H hH PN P hP
    KN hKN K hK hin hinput hlim hconv (hmu.mono fun omega h => ⟨mu omega, h⟩)
  have hconservative : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (P omega).IsConservative := by
    filter_upwards [hlim] with omega hfd
    let Q : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
      K.comap (fun x : SpatialCoordinates d => (omega, x))
        (measurable_const.prodMk measurable_id)
    have hQ : IsMarkovKernel Q := by
      let : IsMarkovKernel K := hK
      dsimp only [Q]
      infer_instance
    apply aux_prop_limit_properties_strong_markov_conservative (P omega) Q hQ
    intro I x
    rw [Kernel.map_apply Q (ContinuousPath.measurable_finsetEvaluation I) x,
      Kernel.comap_apply]
    have h := hfd I x
    rw [Kernel.map_apply K (ContinuousPath.measurable_finsetEvaluation I)
      (omega, x)] at h
    exact h
  refine ⟨H, hH, PN, KN, hKN, hin, hinput, P, K, hK, mu, hmeas, hconv, ?_⟩
  filter_upwards [hlim, hmu, hprops, hconservative] with omega hfdd hm hpr hcons
  exact ⟨hfdd, hm.1, hm.2, hpr.1, hpr.2.1, hcons, hpr.2.2.1,
    hpr.2.2.2 (mu omega) hm.1 hm.2, hpr.2.2.2⟩

end SubdiffusiveProcess.Paper
