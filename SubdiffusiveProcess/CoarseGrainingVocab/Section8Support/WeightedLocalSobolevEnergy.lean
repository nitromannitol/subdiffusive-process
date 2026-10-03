module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyMean

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped ENNReal

/-- The dimension-only constant in the half-order depth estimate. -/
def weightedLocalSobolevDepthEnergyConstant (d : ℕ) [NeZero d] : ℝ :=
  oscillationMultiscalePoincareConstant d * (d : ℝ) *
    ((geometricDiscount (1 / 2) 1)⁻¹ * (d : ℝ))

/-- The dimension-only constant in the zero-trace average estimate. -/
def weightedLocalSobolevMeanEnergyConstant (d : ℕ) [NeZero d] : ℝ :=
  ((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-1))⁻¹)) *
    ((geometricDiscount (1 / 2) 1)⁻¹ * (d : ℝ))

/-- One positive constant pays for oscillations and the zero-trace average. -/
def weightedLocalSobolevEnergyConstant (d : ℕ) [NeZero d] : ℝ :=
  1 + |weightedLocalSobolevDepthEnergyConstant d| +
    |weightedLocalSobolevMeanEnergyConstant d|

theorem weightedEnergy_common_pos (A B : ℝ) : 0 < 1 + |A| + |B| := by
  nlinarith [abs_nonneg A, abs_nonneg B]

theorem weightedEnergy_common_depth (A B S E : ℝ) (hS : 0 ≤ S) (hE : 0 ≤ E) : A * S * E ≤ (1 + |A| + |B|) * S * E := by
  have h : A ≤ 1 + |A| + |B| := by nlinarith [le_abs_self A, abs_nonneg B]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hS) hE

theorem weightedEnergy_common_mean (A B S E : ℝ) (hS : 0 ≤ S) (hE : 0 ≤ E) : S * (B * E) ≤ (1 + |A| + |B|) * S * E := by
  have h : B ≤ 1 + |A| + |B| := by nlinarith [le_abs_self B, abs_nonneg A]
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hS) hE
  convert hm using 1 ; ring

theorem weightedLocalSobolevEnergyConstant_pos (d : ℕ) [NeZero d] :
    0 < weightedLocalSobolevEnergyConstant d :=
  weightedEnergy_common_pos _ _

/-- Uniform dimensional version of the coarse half-order depth estimate. -/
theorem h1_depthSeminorm_half_le_dimensional_energy
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H1Function (openCubeSet Q)) (j : ℕ) :
    cubeBesovDepthSeminorm Q (1 / 2) (2 : ℝ≥0∞) u.toFun j ≤
      weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q *
      Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
        volumeAverage (openCubeSet Q) (fun x => b x * vecDot (u.grad x) (u.grad x))) := by
  have hraw := h1_depthSeminorm_half_le_energy_of_scalarParent Q A b hb u j
  exact hraw.trans (weightedEnergy_common_depth
    (weightedLocalSobolevDepthEnergyConstant d) (weightedLocalSobolevMeanEnergyConstant d)
    _ _ (cubeBesovScaleWeight_nonneg (-1 / 2) Q) (Real.sqrt_nonneg _))

/-- Uniform dimensional bound for the average of a zero-trace function. -/
theorem h10_average_le_dimensional_energy
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H10Function (openCubeSet Q)) :
    |cubeAverage Q u.toH1Function.toFun| ≤
      weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q *
      Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
        volumeAverage (openCubeSet Q)
          (fun x => b x * vecDot (u.toH1Function.grad x) (u.toH1Function.grad x))) := by
  have hraw := h10_average_le_energy_of_scalarParent Q A b hb u
  have hbound := weightedEnergy_common_mean
    (weightedLocalSobolevDepthEnergyConstant d) (weightedLocalSobolevMeanEnergyConstant d)
    (cubeBesovScaleWeight (-1) Q) _ (cubeBesovScaleWeight_nonneg (-1) Q)
    (Real.sqrt_nonneg ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
      volumeAverage (openCubeSet Q)
        (fun x => b x * vecDot (u.toH1Function.grad x) (u.toH1Function.grad x))))
  simpa only [cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor,
    weightedLocalSobolevEnergyConstant] using! hraw.trans hbound

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy

