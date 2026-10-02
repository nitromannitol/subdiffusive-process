import SubdiffusiveProcess.Paper.mfd_thm_c1

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- The proved original-law limit applies to every characterized infrared version.
The change of version uses uniqueness of the same convergent infrared series. -/
theorem aux_mfd_prop_uniform_resolvent_inverse
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, 0 < M.delta → M.delta ≤ delta0 →
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∃ G : KilledInverseFamily d (BilateralField d), (∀ i, Measurable (G i)) ∧
        ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun N omega => volumeResponseOperator (determiningResponseSpace d i)
            (Lane4.cutoffPositiveCoefficient M H omega N
              (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) atTop (G i) := by
  obtain ⟨delta0, hdelta0, hlimit⟩ := aux_mfd_thm_c1_actual_limits d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hMpos hMsmall H hH
  obtain ⟨G, hGmeas, hconv⟩ := hlimit M hMpos hMsmall
  have hcanon : InfraredCharacterization M (comparisonInfrared d hd M) :=
    Classical.choose_spec (exists_infraredCharacterization hd M)
  have hversions : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      comparisonInfrared d hd M omega = H omega := by
    filter_upwards [hcanon.2, hH.2] with omega h1 h2
    exact tendsto_nhds_unique h1 h2
  refine ⟨G, hGmeas, fun i => ?_⟩
  apply TendstoInMeasure.congr_left _ (hconv i)
  intro N
  filter_upwards [hversions] with omega hω
  simp only [representedCutoffInverse, Function.id_def]
  have hCM : Lane4.cutoffCoefficientCM M (comparisonInfrared d hd M) omega N
      (rationalTriadicCenter d i) (rationalTriadicSide_pos d i) =
      Lane4.cutoffCoefficientCM M H omega N
        (rationalTriadicCenter d i) (rationalTriadicSide_pos d i) := by
    ext x
    simp only [Lane4.cutoffCoefficientCM, ContinuousMap.coe_mk,
      cutoffCoefficient, cutoffPotential, hω]
  unfold Lane4.cutoffPositiveCoefficient
  simp only [hCM]

end Paper
