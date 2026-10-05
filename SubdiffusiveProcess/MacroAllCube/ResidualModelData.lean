module

public import SubdiffusiveProcess.MacroAllCube.ResidualModel
public import SubdiffusiveProcess.MacroAllCube.ResidualModelInterface

@[expose] public section

/-!
# The residual model against the  interface

`SubdiffusiveProcess.ResidualModel.residualModel` supplies the fields `model`, `disorder` and
`seed_eq` of `SubdiffusiveProcess.MacroAllCube.ResidualModelData` with `D = residualDisorderFactor d`.
The only field it does not supply is the `n`-uniform homogenized-coefficient
comparison `normalization`; `residualModelData_of_normalization` shows that this
is exactly the remaining obligation.  The exact law transport of the bilateral
sample needs only the seed law, and is proved here without `normalization`.
-/

open MeasureTheory
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model

noncomputable section

namespace SubdiffusiveProcess.ResidualModel

variable {d : ℕ}

/-- **Reduction to the normalization field.**  Any `n`-uniform two-sided
`ahom` comparison for the constructed residual model inhabits the literal 
interface. -/
theorem residualModelData_of_normalization (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s)
    (hs3 : s ≤ 3) (hδ : M.delta ≤ (2 * residualDisorderFactor d)⁻¹) (B : ℝ) (hB : 1 ≤ B)
    (hnorm : ∀ n : ℕ,
      SubdiffusiveProcess.CoarseGrainingVocab.ahom (residualModel M hs1 hs3 hδ) n /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M n ≤ B ∧
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M n /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom (residualModel M hs1 hs3 hδ) n ≤ B) :
    Nonempty (_root_.SubdiffusiveProcess.MacroAllCube.ResidualModelData d M s (residualDisorderFactor d)) :=
  ⟨{ model := residualModel M hs1 hs3 hδ
     disorder := le_of_eq (residualModel_delta M hs1 hs3 hδ)
     seed_eq := residualModel_seed M hs1 hs3 hδ
     B := B
     B_ge_one := hB
     normalization := hnorm }⟩

section ModelLaw

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem chaosRootFieldLaw_residualModel (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s)
    (hs3 : s ≤ 3) (hδ : M.delta ≤ (2 * residualDisorderFactor d)⁻¹) :
    chaosRootFieldLaw (residualModel M hs1 hs3 hδ) =
      _root_.SubdiffusiveProcess.MacroAllCube.residualRootLaw (chaosRootFieldLaw M) s := by
  let forget : C(PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map forget (zeroPotentialLaw (residualModel M hs1 hs3 hδ).P).toMeasure =
    Measure.map (_root_.SubdiffusiveProcess.MacroAllCube.dilateField d s)
      (Measure.map forget (zeroPotentialLaw M.P).toMeasure)
  rw [residualModel_seed, ProbabilityMeasure.toMeasure_map,
    Measure.map_map forget.continuous.measurable
      (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale s).measurable,
    Measure.map_map (_root_.SubdiffusiveProcess.MacroAllCube.dilateField d s).continuous.measurable
      forget.continuous.measurable]
  rfl

/-- **Exact law transport onto the constructed model.**  With `s = r 3^k`, the
bilateral shift `T_{r,k}` carries `chaosSampleLaw M` onto
`chaosSampleLaw M_s`.  No normalization input is used. -/
theorem measurePreserving_residualModel (M : GMCModel d) (r : ℝ) (k : ℕ)
    (hs1 : 1 ≤ r * (3 : ℝ) ^ k) (hs3 : r * (3 : ℝ) ^ k ≤ 3)
    (hδ : M.delta ≤ (2 * residualDisorderFactor d)⁻¹) :
    MeasurePreserving (_root_.SubdiffusiveProcess.MacroAllCube.residualShift (d := d) r k)
      (chaosSampleLaw M).toMeasure
      (chaosSampleLaw (residualModel M hs1 hs3 hδ)).toMeasure := by
  simpa only [chaosSampleLaw, chaosRootFieldLaw_residualModel] using!
    _root_.SubdiffusiveProcess.MacroAllCube.measurePreserving_residualShift (chaosRootFieldLaw M) r k

end ModelLaw

/-- **Headline.**  One dimension-only `D ≥ 1`; for every model with
`M.delta ≤ (2D)⁻¹` and every side `0 < r ≤ 1` there are an integer shift `k`
with `s = r 3^k ∈ (1, 3]` and an actual `GMCModel` `M_s` with disorder
`≤ D * M.delta`, seed law `(zeroPotentialLaw M.P).map (spatialScale s)`, the
same `τ²`, and `T_{r,k}` measure preserving from `chaosSampleLaw M` onto
`chaosSampleLaw M_s`. -/
theorem exists_residualModel_shift (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ M : GMCModel d, M.delta ≤ (2 * D)⁻¹ →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∃ (k : ℕ) (Ms : GMCModel d),
          1 < r * (3 : ℝ) ^ k ∧ r * (3 : ℝ) ^ k ≤ 3 ∧
          Ms.delta ≤ D * M.delta ∧
          zeroPotentialLaw Ms.P =
            (zeroPotentialLaw M.P).map
              (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale (r * (3 : ℝ) ^ k)) ∧
          tauSq Ms.P = tauSq M.P ∧
          MeasurePreserving (_root_.SubdiffusiveProcess.MacroAllCube.residualShift (d := d) r k)
            (chaosSampleLaw M).toMeasure (chaosSampleLaw Ms).toMeasure := by
  refine ⟨residualDisorderFactor d, one_le_residualDisorderFactor d, ?_⟩
  intro M hδ r hr hr1
  obtain ⟨k, hk1, hk3⟩ := _root_.SubdiffusiveProcess.MacroAllCube.exists_residual_scale hr hr1
  exact ⟨k, residualModel M hk1.le hk3 hδ, hk1, hk3,
    le_of_eq (residualModel_delta M hk1.le hk3 hδ),
    residualModel_seed M hk1.le hk3 hδ, residualModel_tauSq M hk1.le hk3 hδ,
    measurePreserving_residualModel M r k hk1.le hk3 hδ⟩

end SubdiffusiveProcess.ResidualModel
