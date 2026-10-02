import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSelectedParameters
import SubdiffusiveProcess.Frozen.Assumptions.GMCModel
/-! Shrinking the disorder constant and enlarging the prefactor preserve the required catalogue tail. -/

set_option autoImplicit false
open MeasureTheory Set
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem goodCube_catalogue_tail_mono
    {d : ℕ} (M : GMCModel d) (c c0 C : ℝ)
    (hc : 0 ≤ c) (hcc0 : c ≤ c0) (hC : 1 ≤ C) :
    ENNReal.ofReal (Real.exp (-(c0^2 / (M.delta^2 * (Real.log M.delta)^2)))) ≤
      ENNReal.ofReal (C * Real.exp
        (-(c * (c / (M.delta^2 * (Real.log M.delta)^2))))) := by
  have h0 : 0 ≤ c0 := le_trans hc hcc0
  have hs : c^2 ≤ c0^2 := by
    have h1 : c * c ≤ c * c0 := mul_le_mul_of_nonneg_left hcc0 hc
    have h2 : c * c0 ≤ c0 * c0 := mul_le_mul_of_nonneg_right hcc0 h0
    linarith [h1, h2]
  have hD : 0 ≤ M.delta^2 * (Real.log M.delta)^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdiv : c^2 / (M.delta^2 * (Real.log M.delta)^2) ≤
      c0^2 / (M.delta^2 * (Real.log M.delta)^2) :=
    div_le_div_of_nonneg_right hs hD
  have hexp : Real.exp (-(c0^2 / (M.delta^2 * (Real.log M.delta)^2))) ≤
      Real.exp (-(c^2 / (M.delta^2 * (Real.log M.delta)^2))) :=
    Real.exp_le_exp.mpr (neg_le_neg hdiv)
  have key : Real.exp (-(c0^2 / (M.delta^2 * (Real.log M.delta)^2))) ≤
      C * Real.exp (-(c^2 / (M.delta^2 * (Real.log M.delta)^2))) := by
    calc Real.exp (-(c0^2 / (M.delta^2 * (Real.log M.delta)^2)))
        = Real.exp (-(c0^2 / (M.delta^2 * (Real.log M.delta)^2))) * 1 :=
          (mul_one _).symm
      _ ≤ Real.exp (-(c^2 / (M.delta^2 * (Real.log M.delta)^2))) * C :=
          mul_le_mul hexp hC zero_le_one (Real.exp_pos _).le
      _ = C * Real.exp (-(c^2 / (M.delta^2 * (Real.log M.delta)^2))) := mul_comm _ _
  have hring : c * (c / (M.delta^2 * (Real.log M.delta)^2))
      = c^2 / (M.delta^2 * (Real.log M.delta)^2) := by ring
  rw [hring]
  exact ENNReal.ofReal_le_ofReal key
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
