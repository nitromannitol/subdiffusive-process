module

public import SubdiffusiveProcess.Frozen.Assumptions.GMCModel
public import SubdiffusiveProcess.Main.ScaledLayerLaw

@[expose] public section

open MeasureTheory
noncomputable section
namespace SubdiffusiveProcess

/-- Stationarity of the actual GMC root field descends to its continuous-map law. -/
theorem gmc_zero_field_law_stationary {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let ν := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
      forget
    ∀ z : SpatialCoordinates d, MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) =>
        f.comp (⟨fun x : SpatialCoordinates d => x + z,
          continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d)))
      ν.toMeasure ν.toMeasure := by
  dsimp only
  intro z
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let translate : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ
      (⟨fun x : SpatialCoordinates d => x + z,
        continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d))
  refine ⟨translate.continuous.measurable, ?_⟩
  let μ := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  let sourceTranslate := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z
  change Measure.map translate (Measure.map forget μ) = Measure.map forget μ
  calc
    Measure.map translate (Measure.map forget μ) =
        Measure.map (translate ∘ forget) μ :=
      Measure.map_map translate.continuous.measurable forget.continuous.measurable
    _ = Measure.map (forget ∘ sourceTranslate) μ := by
      congr 1
    _ = Measure.map forget (Measure.map sourceTranslate μ) :=
      (Measure.map_map forget.continuous.measurable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z)).symm
    _ = Measure.map forget μ := by rw [M.G1.stationary z]

/-- Each natural GMC marginal has exactly the corresponding approved scaled continuous-field law. -/
theorem gmc_marginal_field_law_eq_scaledLayerLaw {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let ν := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
      forget
    (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).map
      forget = scaledLayerLaw d ν (k : ℤ) := by
  dsimp only [scaledLayerLaw]
  rw [M.shellPrefix.marginal_scaling k]
  apply ProbabilityMeasure.toMeasure_injective
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let μ := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  change Measure.map forget
      (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k) μ) =
    Measure.map (layerScaling d (k : ℤ)) (Measure.map forget μ)
  calc
    Measure.map forget
        (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k) μ) =
        Measure.map
          (forget ∘ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k) μ :=
      Measure.map_map forget.continuous.measurable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)
    _ = Measure.map (layerScaling d (k : ℤ) ∘ forget) μ := by
      congr 1
      funext g
      ext x
      change g.1.1 ((((3 : ℝ) ^ k)⁻¹) • x) =
        g.1.1 ((3 : ℝ) ^ (-(k : ℤ)) • x)
      rw [zpow_neg, zpow_natCast]
    _ = Measure.map (layerScaling d (k : ℤ)) (Measure.map forget μ) :=
      (Measure.map_map (layerScaling d (k : ℤ)).continuous.measurable
        forget.continuous.measurable).symm

end SubdiffusiveProcess
