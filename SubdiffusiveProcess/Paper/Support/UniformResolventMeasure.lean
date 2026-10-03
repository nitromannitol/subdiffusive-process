module

public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Lane1.SpeedBasic
public import SubdiffusiveProcess.Section9.RepresentedComparisonDraft

@[expose] public section

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

/-- Produce the actual speed measure and measurable growth constants of any
requested integer moment order, with the disorder chosen before every region. -/
theorem aux_mfd_prop_uniform_resolvent_measure
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (p : ℕ) (hp : (d : ℝ) < p * epsilon) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ muFull : BilateralField d → Measure (SpatialCoordinates d),
        Measurable muFull ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          IsLocallyFiniteMeasure (muFull omega) ∧ (muFull omega).IsOpenPosMeasure ∧
          NoAtoms (muFull omega) ∧
          ∀ i, muFull omega (frontier (determiningCube d i : Set (SpatialCoordinates d))) = 0) ∧
        ∀ (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
          ∃ Kmu : BilateralField d → ℝ,
            Measurable Kmu ∧ MemLp Kmu p (chaosSampleLaw M).toMeasure ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              0 ≤ Kmu omega ∧
              (∀ N x, x ∈ Region → ∀ r, 0 < r → r ≤ 1 →
                cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon))) ∧
              (∀ x, x ∈ Region → ∀ r, 0 < r → r ≤ 1 →
                muFull omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon))) := by
  obtain ⟨delta0, hdelta0, hgrowth⟩ := prop_chaos_growth hd epsilon hepsilon p hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M H hH hM
  obtain ⟨muFull, hmeas, hlimit, hregions⟩ := hgrowth M H hH hM
  refine ⟨muFull, hmeas, ?_, ?_⟩
  · filter_upwards [hlimit] with omega hω
    refine ⟨?_, hω.2.1, hω.2.2.1, hω.2.2.2.1, fun i => ?_⟩
    · simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using hω.1
    · exact hω.2.2.2.2 (rationalTriadicCenter d i) (rationalTriadicSide d i)
        (rationalTriadicSide_pos d i)
  · intro Region hRegion
    obtain ⟨K, hKmem, hK⟩ := hregions Region hRegion
    let Kmu := hKmem.aestronglyMeasurable.mk K
    have hKae : K =ᵐ[(chaosSampleLaw M).toMeasure] Kmu :=
      hKmem.aestronglyMeasurable.ae_eq_mk
    refine ⟨Kmu, hKmem.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      hKmem.ae_eq hKae, ?_⟩
    filter_upwards [hK, hKae] with omega hω hEq
    rw [← hEq]
    simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using hω

end Paper
