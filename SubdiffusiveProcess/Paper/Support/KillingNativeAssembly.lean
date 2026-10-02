import SubdiffusiveProcess.Paper.prop_limit_properties
import SubdiffusiveProcess.Paper.Support.KillingProducedData

/-! Supports: mfd_lem_killing.
Internal assembly using the native limit-property producer and the actual produced
form bank. The source principal discharges this bank with FIVE-2; no bank or
predecessor conclusion is a premise of that principal.
-/
open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_lem_killing_of_produced_bank
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (deltaR : ℝ) (hdeltaR : 0 < deltaR)
    (hbank : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaR →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
      ∃ muFull : BilateralField d → Measure (SpatialCoordinates d),
        Measurable muFull ∧ SubdiffusiveProcess.Section9.KilledFormResolventData d hd M H KN muFull) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∃ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H)
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
              IsLocallyFiniteMeasure nu → SemigroupSymmetric (P omega) nu)) ∧
          SubdiffusiveProcess.Section9.KilledFormResolventIdentification d hd M H KN K mu :=
 by
  classical
  obtain ⟨deltaP, hdeltaP, hlimit⟩ := prop_limit_properties hd
  refine ⟨min deltaP deltaR, lt_min hdeltaP hdeltaR, ?_⟩
  intro M hM
  obtain ⟨H, hH, PN, KN, hKN, hin, hinput, P, K, hK, _muP,
    _hmuPmeas, hpath, hprops⟩ := hlimit M (hM.trans (min_le_left _ _))
  obtain ⟨muFull, hmumeas, hform⟩ :=
    hbank M (hM.trans (min_le_right _ _)) H hH PN KN hKN hin
  have hmu : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      IsLocallyFiniteMeasure (muFull omega) := by
    rcases hform with ⟨_G, _hGmeas, _hGconv, hm, _⟩
    filter_upwards [hm] with omega ho
    exact ⟨ho.1, ho.2.1⟩
  have hid := aux_mfd_lem_killing_identify_produced_data hd M H PN KN hKN K hK hin hpath
    muFull hform
  refine ⟨H, hH, PN, KN, hKN, hin, hinput, P, K, hK, muFull,
    hmumeas, hpath, ?_, hid⟩
  filter_upwards [hprops, hmu] with omega hp hm
  rcases hp with ⟨hfdd, _hconv, _hlf, hcont, hFeller, hcons, hMarkov, _hsym, hsymAll⟩
  exact ⟨hfdd, hm.1, hm.2, hcont, hFeller, hcons, hMarkov,
    hsymAll (muFull omega) hm.1 hm.2, hsymAll⟩

end Paper
