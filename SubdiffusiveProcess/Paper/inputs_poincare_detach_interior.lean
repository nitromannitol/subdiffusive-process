module

public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import SubdiffusiveProcess.Besov.DetachMain

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_poincare_detach_interior (d : ℕ) (hd : 2 ≤ d) :
    (∃ C : ℝ, 0 < C ∧
      (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ H : Homogenization.H1Function
          (Homogenization.openCubeSet (Homogenization.originCube d 0)),
          ∀ hu : Homogenization.ExactOverlapIntegrable
            (Homogenization.originCube d 0) H.toFun,
            (iSup fun j : ℕ =>
              Homogenization.exactOverlapDepthTerm
                (Homogenization.originCube d 0) (1 - s) 2 H.toFun hu j).toReal ≤
              C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                (Homogenization.originCube d 0) s (.finite 1) H.grad)) := by
  haveI : NeZero d := ⟨by omega⟩
  exact SubdiffusiveProcess.Besov.Detach.detach_main d

end Paper

