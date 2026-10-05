module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannHessianPackage
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFinalSpecialization
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionGeometry

@[expose] public section




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Concentric open subcubes are monotone in the relative radius. -/
theorem scaledOpenCubeSet_mono (Q : TriadicCube d) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    scaledOpenCubeSet Q r₁ ⊆ scaledOpenCubeSet Q r₂ := by
  intro x hx i
  exact lt_of_lt_of_le (hx i)
    (mul_le_mul_of_nonneg_right h (cubeRadius_nonneg Q))



theorem openCubeSet_subset_scaledOpenCubeSet_succ_half (d : ℕ) (m : ℤ) :
    openCubeSet (originCube d m) ⊆
      scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ) := by
  rw [← scaledOpenCubeSet_originCube_succ_one_div_three d m]
  exact scaledOpenCubeSet_mono _ (by norm_num)

/-- Every one-step source cell of `originCube d K` satisfies the `hRhalf`
hypothesis of the Neumann Hessian package for the parent
`originCube d (K + 1)`. -/
theorem openCubeSet_sourceCell_subset_scaledOpenCubeSet_succ_half
    {K n : ℕ} {delta : ℝ} {R : TriadicCube d}
    (hR : R ∈ oneStepSourceCells d K n delta) :
    openCubeSet R ⊆
      scaledOpenCubeSet (originCube d ((K : ℤ) + 1)) (1 / 2 : ℝ) :=
  (openCubeSet_subset_of_mem_descendantsAtDepth
    (mem_oneStepSourceCells hR)).trans
      (openCubeSet_subset_scaledOpenCubeSet_succ_half d (K : ℤ))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
