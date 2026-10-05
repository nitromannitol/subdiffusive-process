module

public import SubdiffusiveProcess.Section10.SpatialVagueBorel
public import SubdiffusiveProcess.Section10.LimitMeasureRescaledLawClassicalConsumer
public import SubdiffusiveProcess.Section10.LimitMeasureLawsAssembly

@[expose] public section

/-! The now-proved P1 is consumed by the existing actual finite-law/DCT
transport. The measure witness and its density/spatial/growth laws are kept. -/

open MeasureTheory SubdiffusiveProcess Filter Topology
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

instance instSpatialVagueBorelSpace (d : ℕ) : BorelSpace (LocallyFiniteSpatialMeasure d) :=
  ⟨spatialVagueTopology_borel_eq d⟩

/-- No Borel identity premise remains: apply P1 to the supplied SAME actual
unweighted chaos limit and the literal vaguely topologized measure carrier. -/
theorem localRescaledCutoffLaw_tendsto {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)) (hm : Measurable mu0)
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w)) :
    Tendsto (localRescaledCutoffLaw M) atTop (𝓝 (localLimitLaw M mu0 hl hm)) :=
  localRescaledCutoffLaw_tendsto_of_vague_borel_eq (spatialVagueTopology_borel_eq d)
    M mu0 hl hm hc

/-- Concrete actual-model consumer: preserve the retained density-divergence
and spatial-law witness, and add convergence of its rescaled cutoff laws. -/
theorem exists_same_limit_spatial_growth_rescaledLaw {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∃ (mu0 : BilateralField d → Measure (SpatialCoordinates d))
      (hm : Measurable mu0) (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)),
      Measurable (infraredWeightedLimit H mu0) ∧
      (∀ w, IsLocallyFiniteMeasure (infraredWeightedLimit H mu0 w)) ∧
      (∀ᵐ w ∂(chaosSampleLaw M).toMeasure, SameLimitDensityProperties M H mu0 w) ∧
      SameLimitSpatialLaws M mu0 ∧ SameLimitGrowthMoments M H mu0 p ∧
      (∀ᵐ w ∂(chaosSampleLaw M).toMeasure, SameLimitGrowth H mu0 w) ∧
      Tendsto (localRescaledCutoffLaw M) atTop (𝓝 (localLimitLaw M mu0 hl hm)) := by
  obtain ⟨delta0, hd0, hlim⟩ := exists_same_limit_density_spatial_growth hd p hp
  refine ⟨delta0, hd0, ?_⟩
  intro M H hH hdelta
  obtain ⟨mu0, hm, hwm, hl, hwl, hdensity, hspatial, hmoment, hgrowth⟩ :=
    hlim M H hH hdelta
  exact ⟨mu0, hm, hl, hwm, hwl, hdensity, hspatial, hmoment, hgrowth,
    localRescaledCutoffLaw_tendsto M mu0 hl hm (hdensity.mono fun w hw => hw.1)⟩

end SubdiffusiveProcess.Section10
