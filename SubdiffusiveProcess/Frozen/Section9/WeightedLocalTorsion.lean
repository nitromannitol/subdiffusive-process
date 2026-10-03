module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Providers.Section9.WeightedLocalTorsion
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal NNReal
noncomputable section





theorem SubdiffusiveProcess.Frozen.Section9.weighted_local_torsion {d : ℕ}
    (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d)) (clock : ℝ → ℝ)
    (p0 cc CC : ℝ) (U : Cube d) (Qfam Afam : Set (Cube d))
    (hgood : LocalTorsionEstimates a law clock p0 cc CC U Qfam Afam) :
    (∀ x ∈ middleQuarter U,
        ENNReal.ofReal (cc * clock U.2) ≤ meanExit law (cubeSet U) x) ∧
      (∀ x ∈ cubeSet U, meanExit law (cubeSet U) x ≤ ENNReal.ofReal (CC * clock U.2)) ∧
      (∀ B' ∈ Qfam, ∀ B ∈ Qfam, CompactlyInside B' B →
        (∀ x ∈ cubeSet B', ENNReal.ofReal (cc * clock B.2) ≤ meanExit law (cubeSet B) x) ∧
          (∀ x ∈ cubeSet B, meanExit law (cubeSet B) x ≤ ENNReal.ofReal (CC * clock B.2))) ∧
      (ENNReal.ofReal cc * weightedMeasure a (cubeSet U) ≤
        weightedMeasure a (middleQuarter U)) ∧
      (∀ B' ∈ Qfam, ∀ B ∈ Qfam, CompactlyInside B' B →
        ENNReal.ofReal cc * weightedMeasure a (cubeSet B) ≤ weightedMeasure a (cubeSet B')) ∧
      (∀ A ∈ Afam,
        ENNReal.ofReal cc * weightedMeasure a (cubeSet U) ≤ weightedMeasure a (cubeSet A)) ∧
      (∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
        lpSq a (cubeSet Q) p0 f.toH1Function.toFun ≤
          ENNReal.ofReal CC * weightedMeasure a (cubeSet Q) ^ (-(1 - 2 / p0)) *
            ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function))

:= SubdiffusiveProcess.Providers.Section9.weighted_local_torsion a law clock p0 cc CC U Qfam Afam hgood
