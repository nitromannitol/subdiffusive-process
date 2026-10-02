import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Main.CommonScaleLaw

open MeasureTheory

noncomputable section

namespace SubdiffusiveProcess

/-- Independent native root-field copies, scaled by the approved layer maps, realize the
common-scale product law exactly. -/
theorem measurePreserving_nativeCopies_commonScaleLaw
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let ν := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
      forget.continuous.measurable.aemeasurable
    MeasurePreserving
      (fun ω : ℤ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        fun j => layerScaling d j (forget (ω j)))
      (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))
      (commonScaleLaw d ν).toMeasure := by
  dsimp only
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let μ := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  let ν := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
    forget.continuous.measurable.aemeasurable
  refine ⟨?_, ?_⟩
  · exact measurable_pi_lambda _ (fun j =>
      (layerScaling d j).continuous.measurable.comp
        (forget.continuous.measurable.comp (measurable_pi_apply j)))
  · change Measure.map (fun ω j => layerScaling d j (forget (ω j)))
      (Measure.infinitePi (fun _ : ℤ => μ)) =
      Measure.infinitePi (fun j : ℤ => (scaledLayerLaw d ν j : Measure _))
    rw [Measure.infinitePi_map_pi
      (μ := fun _ : ℤ => μ)
      (f := fun j : ℤ => fun g => layerScaling d j (forget g))
      (fun j => (layerScaling d j).continuous.measurable.comp
        forget.continuous.measurable)]
    congr 1
    funext j
    change Measure.map ((layerScaling d j) ∘ forget) μ =
      Measure.map (layerScaling d j) (Measure.map forget μ)
    rw [← Measure.map_map (layerScaling d j).continuous.measurable
      forget.continuous.measurable]

end SubdiffusiveProcess
