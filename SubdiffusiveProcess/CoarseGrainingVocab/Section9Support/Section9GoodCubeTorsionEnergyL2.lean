import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyFinish
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyResidual
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
/-!
# The zero-trace L2 norm from coarse weighted energy

The depth-zero fluctuation and the zero-trace average are controlled by the
same inverse multiscale ellipticity, with a dimension-only constant.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Coarse weighted Poincare estimate for the full zero-trace L2 norm. -/
theorem goodCube_h10_l2_le_coarse_energy
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H10Function (openCubeSet Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) u.toH1Function.toFun ≤
      2 * weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q *
        Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
          volumeAverage (openCubeSet Q) (fun x => b x *
            vecDot (u.toH1Function.grad x) (u.toH1Function.grad x))) := by
  let E := Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
    volumeAverage (openCubeSet Q) (fun x => b x *
      vecDot (u.toH1Function.grad x) (u.toH1Function.grad x)))
  have hu := h1_memLp_normalizedCubeMeasure Q u.toH1Function
  have hres := weightedEnergy_residual_lpNorm_le Q u.toH1Function.toFun
    (weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E)
    hu (fun j => h1_depthSeminorm_half_le_dimensional_energy Q A b hb u.toH1Function j) 0
  have hWsq : cubeBesovScaleWeight (-1 / 2) Q *
      cubeBesovScaleWeight (-1 / 2) Q = cubeScaleFactor Q := by
    rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
    norm_num only [show (-1 / 2 : ℝ) + -1 / 2 = -1 by norm_num]
    exact cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor Q
  have hres0 : cubeLpNorm Q 2 (cubeProjectionResidual Q 0 u.toH1Function.toFun) ≤
      weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q * E := by
    simp only [Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one] at hres
    calc _ ≤ _ := hres
      _ = weightedLocalSobolevEnergyConstant d *
          (cubeBesovScaleWeight (-1 / 2) Q * cubeBesovScaleWeight (-1 / 2) Q) * E := by ring
      _ = _ := by rw [hWsq]
  have hmean := h10_average_le_dimensional_energy Q A b hb u
  have hsum := cubeLpNorm_add_le Q (2 : ℝ≥0∞)
    (cubeProjectionResidual Q 0 u.toH1Function.toFun)
    (cubeProjection Q 0 u.toH1Function.toFun)
    (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.weightedProjection_residual_memLp Q u.toH1Function.toFun 0 hu)
    (cubeProjection_memLp Q 0 2 u.toH1Function.toFun) (by norm_num)
  have hfun : (fun x => cubeProjectionResidual Q 0 u.toH1Function.toFun x +
      cubeProjection Q 0 u.toH1Function.toFun x) = u.toH1Function.toFun := by
    funext x
    simp [cubeProjectionResidual]
  rw [hfun, cubeLpNorm_projection_depth_zero_eq_norm_cubeAverage Q 2
    u.toH1Function.toFun (by norm_num), Real.norm_eq_abs] at hsum
  calc cubeLpNorm Q 2 u.toH1Function.toFun
      ≤ cubeLpNorm Q 2 (cubeProjectionResidual Q 0 u.toH1Function.toFun) +
          |cubeAverage Q u.toH1Function.toFun| := hsum
    _ ≤ weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q * E +
          weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q * E :=
      add_le_add hres0 hmean
    _ = _ := by dsimp only [E]; ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
