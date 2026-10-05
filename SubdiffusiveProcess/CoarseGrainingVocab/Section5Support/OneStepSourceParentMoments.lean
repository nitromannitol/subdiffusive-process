module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSolutionFourthMoment

@[expose] public section

/-!
# Uniform source-block moments for the parent correctors

This module specializes the already proved Dirichlet and Neumann solution
moments to the one-step range `h ≤ delta⁻¹`.  It is the parent-gradient input
to the interior localization at `l.one.step.upper` and `l.one.step.lower` and
`l.one.step.upper` and `l.one.step.lower`; no cell restriction or boundary replacement is asserted here.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Dimension-free fourth-root bound for both normalized parent gradients. -/
def oneStepSourceParentGradientConst : ℝ := oneStepRatioEightUniformConst

theorem oneStepSourceParentGradientConst_pos :
    0 < oneStepSourceParentGradientConst := by
  exact oneStepRatioEightUniformConst_pos

private theorem ratio_bound_four_toReal_le_uniform {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (h : ℕ)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ((ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)).toReal ≤
      oneStepSourceParentGradientConst ^ (4 : ℕ) := by
  have hB0 := oneStepRatioMinusOneEightBound_nonneg M h
  have hBC := oneStepRatioMinusOneEightBound_le_uniform M h hblock
  rw [← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hB0]
  calc
    oneStepRatioMinusOneEightBound M h ^ (4 : ℝ) ≤
        oneStepRatioEightUniformConst ^ (4 : ℝ) :=
      Real.rpow_le_rpow hB0 hBC (by norm_num)
    _ = oneStepSourceParentGradientConst ^ (4 : ℕ) := by
      exact Real.rpow_natCast oneStepRatioEightUniformConst 4

/-- Uniform real fourth moment for the canonical normalized Dirichlet parent
gradient on every origin cube. -/
theorem integral_oneStepOriginDirichletNormalizedGradientFourth_le_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega,
        oneStepOriginDirichletNormalizedGradientFourth M n h p m omega
          ∂M.P.toMeasure ≤
      oneStepSourceParentGradientConst ^ (4 : ℕ) := by
  exact (integral_oneStepOriginDirichletNormalizedGradientFourth_le
    M n h p m hh hp).trans (ratio_bound_four_toReal_le_uniform M h hblock)

/-- Uniform real fourth moment for the canonical normalized Neumann parent
gradient. -/
theorem integral_oneStepOriginNeumannNormalizedGradientFourth_le_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega,
        oneStepOriginNeumannNormalizedGradientFourth M n h p m omega
          ∂M.P.toMeasure ≤
      oneStepSourceParentGradientConst ^ (4 : ℕ) := by
  exact (integral_oneStepOriginNeumannNormalizedGradientFourth_le
    M n h p m hh hp).trans (ratio_bound_four_toReal_le_uniform M h hblock)

/-- The Dirichlet parent fourth-power observable is integrable in the same
uniform block range. -/
theorem integrable_oneStepOriginDirichletNormalizedGradientFourth_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1) :
    Integrable (oneStepOriginDirichletNormalizedGradientFourth M n h p m)
      M.P.toMeasure :=
  integrable_oneStepOriginDirichletNormalizedGradientFourth M n h p m hh hp

/-- Neumann counterpart of the preceding integrability endpoint. -/
theorem integrable_oneStepOriginNeumannNormalizedGradientFourth_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1) :
    Integrable (oneStepOriginNeumannNormalizedGradientFourth M n h p m)
      M.P.toMeasure :=
  integrable_oneStepOriginNeumannNormalizedGradientFourth M n h p m hh hp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
