import SubdiffusiveProcess.MacroAllCube.ResidualLaw
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.CoarseGrainingVocab.Core

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
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s D : ℝ) where
  model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d
  disorder : model.delta ≤ D * M.delta
  seed_eq : SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P =
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale s).measurable.aemeasurable
  B : ℝ
  B_ge_one : 1 ≤ B
  normalization : ∀ n : ℕ,
    SubdiffusiveProcess.CoarseGrainingVocab.ahom model n / SubdiffusiveProcess.CoarseGrainingVocab.ahom M n ≤ B ∧
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M n / SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ≤ B

theorem ResidualModelData.tauSq_eq
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {s D : ℝ}
    (data : ResidualModelData d M s D) :
    SubdiffusiveProcess.Frozen.Assumptions.tauSq data.model.P = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
  unfold SubdiffusiveProcess.Frozen.Assumptions.tauSq
  rw [data.seed_eq, ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale s).measurable.aemeasurable
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0).exp.aestronglyMeasurable)]
  simp only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply, smul_zero]

section ModelLaw

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem ResidualModelData.chaosRootFieldLaw_eq
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {s D : ℝ}
    (data : ResidualModelData d M s D) :
    chaosRootFieldLaw data.model = residualRootLaw (chaosRootFieldLaw M) s := by
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map forget (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw data.model.P).toMeasure =
    Measure.map (dilateField d s)
      (Measure.map forget (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
  rw [data.seed_eq, ProbabilityMeasure.toMeasure_map,
    Measure.map_map forget.continuous.measurable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale s).measurable,
    Measure.map_map (dilateField d s).continuous.measurable forget.continuous.measurable]
  rfl

theorem ResidualModelData.measurePreserving
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (r : ℝ) (k : ℕ) {D : ℝ}
    (data : ResidualModelData d M (r * (3 : ℝ) ^ k) D) :
    MeasurePreserving (residualShift (d := d) r k)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw data.model).toMeasure := by
  simpa only [chaosSampleLaw, data.chaosRootFieldLaw_eq] using
    measurePreserving_residualShift (chaosRootFieldLaw M) r k

end ModelLaw


end MacroAllCube


