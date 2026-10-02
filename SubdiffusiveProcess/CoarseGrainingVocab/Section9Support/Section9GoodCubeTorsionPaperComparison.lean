import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionForcingBesov
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeBesovHalfNorm
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionEnergyL2
set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The actual paper test controls the L2 forcing discrepancy at the coarse ellipticity scale. -/
theorem goodCube_torsion_forcing_l2_comparison_of_paper_test
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (Q : TriadicCube d)
    (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) (scalarCoeffField b))
    (hbL2 : MemL2On (openCubeSet Q) b)
    (h1 : MemL2On (openCubeSet Q) (fun _ : Vec d => (1 : ℝ)))
    (hg : MemLp (fun x => b x - 1) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hf : ExactCircIntegrable Q (fun x => b x - 1))
    {zeta : ℝ} (hzeta : 0 ≤ zeta)
    (hBesov : ENNReal.ofReal ((3 : ℝ) ^ (-((Q.scale : ℝ) / 8))) *
      paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ)) (fun x => b x - 1) hf ≤
        ENNReal.ofReal zeta)
    (e w : H10Function (openCubeSet Q))
    (he : IsMassiveWeakSolutionOn b b 0 (openCubeSet Q) e.toH1Function (fun _ => 1))
    (hw : IsMassiveWeakSolutionOn b (fun _ => 1) 0 (openCubeSet Q) w.toH1Function (fun _ => 1)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (e - w).toH1Function.toFun ≤
      32 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * (weightedLocalSobolevEnergyConstant d) ^ 2 *
        (1 - (3 : ℝ) ^ (-(3 / 8 : ℝ)))⁻¹ * zeta * (cubeScaleFactor Q) ^ 2 *
          (Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ := by
  have hC : 0 ≤ weightedLocalSobolevEnergyConstant d :=
    (weightedLocalSobolevEnergyConstant_pos d).le
  have hS : 0 ≤ cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  have hW : 0 ≤ cubeBesovScaleWeight (-1 / 2) Q :=
    cubeBesovScaleWeight_nonneg _ Q
  have hgeo : 0 ≤ (1 - (3 : ℝ) ^ (-(3 / 8 : ℝ)))⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)).le)
  have hL : 0 ≤ (Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_finite_pos Q A (by norm_num) (by norm_num)).le
  have hnorm := goodCube_negative_half_norm_le_paper_test hd Q (fun x => b x - 1)
    hg hf hzeta hBesov
  have hB : 0 ≤ 8 * (1 - (3 : ℝ) ^ (-(3 / 8 : ℝ)))⁻¹ * zeta *
      cubeBesovScaleWeight (-1 / 2) Q := by positivity
  have henergy := goodCube_torsion_comparison_of_half_besov_bound
    Q A b hb hEll hbL2 h1 hg hB hnorm e w he hw
  have hl2 := goodCube_h10_l2_le_coarse_energy Q A b hb (e - w)
  rw [Real.sqrt_mul hL] at hl2
  have hcoeff : 0 ≤ 2 * weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q *
      Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹) := by positivity
  have hWsq : cubeBesovScaleWeight (-1 / 2) Q *
      cubeBesovScaleWeight (-1 / 2) Q = cubeScaleFactor Q := by
    rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
    norm_num only [show (-1 / 2 : ℝ) + -1 / 2 = -1 by norm_num]
    exact cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor Q
  calc cubeLpNorm Q (2 : ℝ≥0∞) (e - w).toH1Function.toFun
      ≤ (2 * weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q *
          Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹)) *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x =>
            b x * vecNormSq ((e - w).toH1Function.grad x))) := by
        simpa only [vecNormSq, mul_assoc] using hl2
    _ ≤ (2 * weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q *
          Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹)) *
        ((2 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * weightedLocalSobolevEnergyConstant d) *
          (8 * (1 - (3 : ℝ) ^ (-(3 / 8 : ℝ)))⁻¹ * zeta * cubeBesovScaleWeight (-1 / 2) Q) *
          cubeBesovScaleWeight (-1 / 2) Q *
          Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹)) :=
      mul_le_mul_of_nonneg_left henergy hcoeff
    _ = (32 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * (weightedLocalSobolevEnergyConstant d) ^ 2 *
          (1 - (3 : ℝ) ^ (-(3 / 8 : ℝ)))⁻¹ * zeta * cubeScaleFactor Q) *
        (cubeBesovScaleWeight (-1 / 2) Q * cubeBesovScaleWeight (-1 / 2) Q) *
        (Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹) *
          Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹)) := by ring
    _ = _ := by rw [hWsq, Real.mul_self_sqrt hL]; ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
