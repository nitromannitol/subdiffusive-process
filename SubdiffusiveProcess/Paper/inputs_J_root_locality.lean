module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_J_root_locality (d : ℕ) [NeZero d] (Q : Homogenization.TriadicCube d) (A B : Homogenization.Book.Ch02.TriadicCoeffFamily d) (hAB : Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q)) :
    (∀ (s : ℝ) (q : Homogenization.Book.Ch02.MultiscaleExponent),
       Homogenization.Book.Ch02.lambdaSq Q s q A = Homogenization.Book.Ch02.lambdaSq Q s q B ∧
       Homogenization.Book.Ch02.LambdaSq Q s q A = Homogenization.Book.Ch02.LambdaSq Q s q B) := by
  have hDesc : ∀ (k : ℤ) (S : Homogenization.TriadicCube d),
      S ∈ Homogenization.descendantsAtScale Q k →
      Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S) := by
    intro k S hS
    have hk : k ≤ Q.scale :=
      Homogenization.descendant_scale_le_of_mem_descendantsAtScale hS
    have hA := A.restrictsTo_descendant hk hS
    have hB := B.restrictsTo_descendant hk hS
    have hAB_S : A.coeffOn Q =ᵐ[volume.restrict (Homogenization.openCubeSet S)]
        B.coeffOn Q := by
      exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hS) hAB
    change A.coeffOn S =ᵐ[volume.restrict (Homogenization.openCubeSet S)]
      B.coeffOn S
    exact hA.trans (hAB_S.trans hB.symm)
  intro s q
  constructor
  · exact SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.lambdaSq_eq_of_descendantAEEq
      Q hDesc s q
  · exact SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.LambdaSq_eq_of_descendantAEEq
      Q hDesc s q

end SubdiffusiveProcess.Paper

