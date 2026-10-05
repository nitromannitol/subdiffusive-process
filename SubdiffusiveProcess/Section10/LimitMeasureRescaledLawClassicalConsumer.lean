module

public import SubdiffusiveProcess.Section10.LimitMeasureRescaledLawVagueTopology
public import SubdiffusiveProcess.Section10.LimitMeasureRescaledLawTransfer
public import SubdiffusiveProcess.Section10.LimitMeasureGrowthConsumer

@[expose] public section

/-! Internal conditional application of one exact classical input: the
inherited evaluation sigma-algebra equals the Borel sigma-algebra of the
literal vague topology. No inhabitant of that input is asserted here.
The topology, its convergence characterization, finite equality in law,
and dominated-convergence law transfer are all completed providers. -/

open MeasureTheory SubdiffusiveProcess Filter Topology Set
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10



theorem localRescaledCutoffLaw_tendsto_of_vague_borel_eq {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hB : (inferInstance : MeasurableSpace (LocallyFiniteSpatialMeasure d)) =
      @borel (LocallyFiniteSpatialMeasure d) (spatialVagueTopology d))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)) (hm : Measurable mu0)
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w)) :
    letI : BorelSpace (LocallyFiniteSpatialMeasure d) := ⟨hB⟩
    Tendsto (localRescaledCutoffLaw M) atTop (𝓝 (localLimitLaw M mu0 hl hm)) := by
  have : BorelSpace (LocallyFiniteSpatialMeasure d) := ⟨hB⟩
  apply localRescaledCutoffLaw_tendsto_of_ae_tendsto M mu0 hl hm
  filter_upwards [hc] with w hw
  exact (tendsto_spatialVagueTopology_iff
    (fun n => localChaosCutoff M n w) (localMeasureRepresentative mu0 hl w)).mpr hw

/-- Concrete conditional consumer choosing the very same representative
from the completed density-divergence and growth bundle. The disorder
threshold still precedes the model, infrared field and bounded window;
all earlier measure, event and moment conclusions are retained. -/
theorem exists_same_limit_growth_rescaledLaw_of_vague_borel_eq {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hB : (inferInstance : MeasurableSpace (LocallyFiniteSpatialMeasure d)) =
      @borel (LocallyFiniteSpatialMeasure d) (spatialVagueTopology d))
    (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) :
    letI : BorelSpace (LocallyFiniteSpatialMeasure d) := ⟨hB⟩
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (mu0 : BilateralField d → Measure (SpatialCoordinates d))
        (hm : Measurable mu0) (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)),
        Measurable (infraredWeightedLimit H mu0) ∧
        (∀ w, IsLocallyFiniteMeasure (infraredWeightedLimit H mu0 w)) ∧
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w) ∧
          mu0 w ⟂ₘ volume ∧
          (∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
            Tendsto (fun n => fineDensity M n w x) atTop (𝓝 0)) ∧
          (∀ᵐ x ∂mu0 w, Tendsto (fun n => fineDensity M n w x) atTop atTop) ∧
          MeasuresConvergeLocally (fun n => weightedChaosCutoff M H n w)
            (infraredWeightedLimit H mu0 w) ∧
          infraredWeightedLimit H mu0 w ⟂ₘ volume ∧
          (∀ᵐ x ∂infraredWeightedLimit H mu0 w,
            Tendsto (fun n => fineDensity M n w x) atTop atTop)) ∧
        (∀ D : Set (SpatialCoordinates d), MeasurableSet D →
          (∫⁻ w, mu0 w D ∂(chaosSampleLaw M).toMeasure) = volume D) ∧
        (¬ ∃ m : Measure (SpatialCoordinates d),
          ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, mu0 w = m) ∧
        (∀ R : Set (SpatialCoordinates d), Bornology.IsBounded R →
          ∃ K : BilateralField d → ℝ, Measurable K ∧
            MemLp K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
            (∀ w, 0 ≤ K w) ∧
            ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
              ∀ x ∈ R, ∀ r : ℝ, 0 < r → r ≤ 1 →
                mu0 w (Metric.ball x r) + infraredWeightedLimit H mu0 w (Metric.ball x r)
                  ≤ ENNReal.ofReal (K w * r ^ ((d : ℝ) - 1 / 2))) ∧
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) n,
              ∀ r : ℝ, 0 < r → r ≤ 1 →
                mu0 w (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2)) ∧
                infraredWeightedLimit H mu0 w (Metric.ball x r)
                  ≤ ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2))) ∧
        Tendsto (localRescaledCutoffLaw M) atTop (𝓝 (localLimitLaw M mu0 hl hm)) := by
  have : BorelSpace (LocallyFiniteSpatialMeasure d) := ⟨hB⟩
  obtain ⟨delta0, hd0, hg⟩ := exists_same_limit_density_divergence_growth hd p hp
  refine ⟨delta0, hd0, ?_⟩
  intro M H hH hdelta
  obtain ⟨mu0, hm, hwm, hl, hwl, hall, hmean, hnd, hbank, hquenched⟩ :=
    hg M H hH hdelta
  exact ⟨mu0, hm, hl, hwm, hwl, hall, hmean, hnd, hbank, hquenched,
    localRescaledCutoffLaw_tendsto_of_vague_borel_eq hB M mu0 hl hm
      (hall.mono fun w hw => hw.1)⟩

end SubdiffusiveProcess.Section10
