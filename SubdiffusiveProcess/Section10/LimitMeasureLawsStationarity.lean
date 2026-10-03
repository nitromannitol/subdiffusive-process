module

public import SubdiffusiveProcess.Section10.ChaosLimitLaws
public import SubdiffusiveProcess.Section10.ChaosVagueMartingale
public import SubdiffusiveProcess.Section10.VagueWeights

@[expose] public section

/-!
# Stationarity of the same actual unweighted chaos limit

Source: `lim:thm-measure` (i). Spatial translation is transported through
compactly supported tests, not through arbitrary Borel restrictions. The
actual-model theorem applies to the supplied measurable locally finite limit
of `chaosCutoff M N`; it assumes no stationarity property of that limit.
-/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology
open scoped CompactlySupported ENNReal

noncomputable section

namespace SubdiffusiveProcess.Section10

/-- A homeomorphism transports locally weak convergence, since its pullback
preserves continuous compactly supported tests. -/
theorem locally_weak_convergence_map_homeomorph
    {d : ℕ} (muN : ℕ → Measure (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d))
    (hc : MeasuresConvergeLocally muN mu)
    (e : SpatialCoordinates d ≃ₜ SpatialCoordinates d) :
    MeasuresConvergeLocally (fun N => (muN N).map e) (mu.map e) := by
  intro f
  let g : C_c(SpatialCoordinates d, ℝ) :=
    ⟨⟨fun x => f (e x), f.continuous.comp e.continuous⟩,
      f.hasCompactSupport.comp_homeomorph e⟩
  have hmap (nu : Measure (SpatialCoordinates d)) :
      (∫ x, f x ∂nu.map e) = ∫ x, g x ∂nu :=
    integral_map e.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable
  simpa only [hmap] using hc g

/-- The actual same chaos limit is equivariant almost surely under each
literal bilateral spatial shift. No new random measure is constructed. -/
theorem same_chaos_limit_translation_ae
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 omega))
    (hc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N omega) (mu0 omega))
    (y : SpatialCoordinates d) :
    (fun omega => mu0 (Paper.aux_lim_measure_bilateralShift (-y) omega))
      =ᵐ[(chaosSampleLaw M).toMeasure] fun omega => (mu0 omega).map (fun x => x + y) := by
  have hshift := Paper.aux_lim_measure_chaosSampleLaw_spatialShift M (-y)
  have hlshift := hshift.quasiMeasurePreserving.ae hl
  have hcshift := hshift.quasiMeasurePreserving.ae hc
  filter_upwards [hl, hc, hlshift, hcshift] with omega hloc hconv hlocshift hconvshift
  letI : IsLocallyFiniteMeasure (mu0 omega) := hloc
  letI : IsLocallyFiniteMeasure (mu0 (Paper.aux_lim_measure_bilateralShift (-y) omega)) :=
    hlocshift
  let e : SpatialCoordinates d ≃ₜ SpatialCoordinates d := Homeomorph.addRight y
  letI : ((mu0 omega).map e).Regular := Measure.Regular.map e
  have htranslated := locally_weak_convergence_map_homeomorph _ _ hconv e
  have hsequence : (fun N => chaosCutoff M N
      (Paper.aux_lim_measure_bilateralShift (-y) omega)) =
      fun N => (chaosCutoff M N omega).map e := by
    funext N
    exact Paper.aux_lim_measure_chaosCutoff_spatialShift M N omega y
  rw [hsequence] at hconvshift
  have heq : mu0 (Paper.aux_lim_measure_bilateralShift (-y) omega) = (mu0 omega).map e :=
    Paper.aux_lim_measure_vague_unique _ _ _ hconvshift htranslated
  exact heq



theorem same_chaos_limit_stationary
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 omega))
    (hc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N omega) (mu0 omega)) :
    ∀ y : SpatialCoordinates d,
      (chaosSampleLaw M).toMeasure.map (fun omega => (mu0 omega).map (fun x => x + y)) =
        (chaosSampleLaw M).toMeasure.map mu0 := by
  intro y
  have hshift := Paper.aux_lim_measure_chaosSampleLaw_spatialShift M (-y)
  calc
    (chaosSampleLaw M).toMeasure.map (fun omega => (mu0 omega).map (fun x => x + y)) =
        (chaosSampleLaw M).toMeasure.map
          (mu0 ∘ Paper.aux_lim_measure_bilateralShift (-y)) :=
      Measure.map_congr (same_chaos_limit_translation_ae M mu0 hl hc y).symm
    _ = ((chaosSampleLaw M).toMeasure.map
          (Paper.aux_lim_measure_bilateralShift (-y))).map mu0 :=
      (Measure.map_map hm hshift.measurable).symm
    _ = (chaosSampleLaw M).toMeasure.map mu0 := by rw [hshift.map_eq]



theorem exists_actual_chaos_limit_stationary
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∃ mu0 : BilateralField d → Measure (SpatialCoordinates d), Measurable mu0 ∧
      (∀ omega, IsLocallyFiniteMeasure (mu0 omega)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        MeasuresConvergeLocally (fun N => chaosCutoff M N omega) (mu0 omega)) ∧
      ∀ y : SpatialCoordinates d,
        (chaosSampleLaw M).toMeasure.map (fun omega => (mu0 omega).map (fun x => x + y)) =
          (chaosSampleLaw M).toMeasure.map mu0 := by
  obtain ⟨mu0, hm, hl, hc⟩ := Paper.aux_lim_measure_exists_unweighted_vague_limit M
  exact ⟨mu0, hm, hl, hc, same_chaos_limit_stationary M mu0 hm (ae_of_all _ hl) hc⟩

end SubdiffusiveProcess.Section10
