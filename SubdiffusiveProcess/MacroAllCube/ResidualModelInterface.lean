module

public import SubdiffusiveProcess.MacroAllCube.ResidualLaw
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.Core

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess
noncomputable section
namespace MacroAllCube
variable {d : ℕ}

/-- Data that an actual bounded-dilation model constructor must produce.
There is deliberately no asserted inhabitant here. This is not an added
hypothesis of any frozen theorem. The normalization comparison is the
minimal one needed for the all-cube moment argument; exact invariance
would supply it with `B = 1`. -/
structure ResidualModelData (d : ℕ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s D : ℝ) where
  model : _root_.SubdiffusiveProcess.Model.GMCModel d
  disorder : model.delta ≤ D * M.delta
  seed_eq : _root_.SubdiffusiveProcess.Model.zeroPotentialLaw model.P =
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
      (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale s)
  B : ℝ
  B_ge_one : 1 ≤ B
  normalization : ∀ n : ℕ,
    SubdiffusiveProcess.CoarseGrainingVocab.ahom model n / SubdiffusiveProcess.CoarseGrainingVocab.ahom M n ≤ B ∧
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M n / SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ≤ B

theorem ResidualModelData.tauSq_eq
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {s D : ℝ}
    (data : ResidualModelData d M s D) :
    _root_.SubdiffusiveProcess.Model.tauSq data.model.P = _root_.SubdiffusiveProcess.Model.tauSq M.P := by
  unfold _root_.SubdiffusiveProcess.Model.tauSq
  rw [data.seed_eq, ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale s).measurable.aemeasurable
    ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).exp.aestronglyMeasurable)]
  simp only [_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_zero]

section ModelLaw

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem ResidualModelData.chaosRootFieldLaw_eq
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {s D : ℝ}
    (data : ResidualModelData d M s D) :
    chaosRootFieldLaw data.model = residualRootLaw (chaosRootFieldLaw M) s := by
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map forget (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw data.model.P).toMeasure =
    Measure.map (dilateField d s)
      (Measure.map forget (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  rw [data.seed_eq, ProbabilityMeasure.toMeasure_map,
    Measure.map_map forget.continuous.measurable
      (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale s).measurable,
    Measure.map_map (dilateField d s).continuous.measurable forget.continuous.measurable]
  rfl

theorem ResidualModelData.measurePreserving
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} (r : ℝ) (k : ℕ) {D : ℝ}
    (data : ResidualModelData d M (r * (3 : ℝ) ^ k) D) :
    MeasurePreserving (residualShift (d := d) r k)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw data.model).toMeasure := by
  simpa only [chaosSampleLaw, data.chaosRootFieldLaw_eq] using!
    measurePreserving_residualShift (chaosRootFieldLaw M) r k

end ModelLaw


end MacroAllCube


