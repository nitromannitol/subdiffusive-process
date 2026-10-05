module

public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Main.CommonScaleLaw

@[expose] public section

open MeasureTheory

noncomputable section

namespace SubdiffusiveProcess

/-- Independent native root-field copies, scaled by the specified layer maps, realize the
common-scale product law exactly. -/
theorem measurePreserving_nativeCopies_commonScaleLaw
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let ν := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
      forget
    MeasurePreserving
      (fun ω : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d =>
        fun j => layerScaling d j (forget (ω j)))
      (Measure.infinitePi (fun _ : ℤ =>
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure))
      (commonScaleLaw d ν).toMeasure := by
  dsimp only
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let μ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let ν := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
    forget
  refine ⟨?_, ?_⟩
  · exact Measurable.of_eval (fun j : ℤ =>
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
