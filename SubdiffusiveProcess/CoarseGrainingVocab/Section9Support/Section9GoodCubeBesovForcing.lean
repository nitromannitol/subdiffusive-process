import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyFinish
import Homogenization.Besov.Duality.CaccioppoliBridge
import Homogenization.Besov.Negative.ExactFiniteBridge
/-!
# Half-order Besov pairing against the weighted energy

The full positive Besov test norm retains the average of the zero-trace
function. Consequently the forcing term needs no mean-zero hypothesis.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Half-order negative Besov norm controls the forcing pairing in weighted energy. -/
theorem goodCube_half_besov_pairing_le_energy
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (g : Vec d → ℝ) (hg : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (u : H10Function (openCubeSet Q)) :
    |cubeAverage Q (fun x => g x * u.toH1Function.toFun x)| ≤
      (2 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * weightedLocalSobolevEnergyConstant d) *
        cubeBesovCircNorm Q (1 / 2) (2 : ℝ≥0∞) (1 : ℝ≥0∞) g *
        cubeBesovScaleWeight (-1 / 2) Q *
        Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
          volumeAverage (openCubeSet Q) (fun x => b x *
            vecDot (u.toH1Function.grad x) (u.toH1Function.grad x))) := by
  set E : ℝ :=
    Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
      volumeAverage (openCubeSet Q) (fun x => b x *
        vecDot (u.toH1Function.grad x) (u.toH1Function.grad x))) with hE
  have hCpos : 0 < weightedLocalSobolevEnergyConstant d :=
    weightedLocalSobolevEnergyConstant_pos d
  have hSnn : 0 ≤ cubeBesovScaleWeight (-1 / 2) Q :=
    cubeBesovScaleWeight_nonneg (-1 / 2) Q
  have hEnn : 0 ≤ E := by
    rw [hE]
    exact Real.sqrt_nonneg _
  have hB : 0 ≤ 2 * weightedLocalSobolevEnergyConstant d *
      cubeBesovScaleWeight (-1 / 2) Q * E := by
    have h2C : 0 ≤ 2 * weightedLocalSobolevEnergyConstant d :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCpos.le
    exact mul_nonneg (mul_nonneg h2C hSnn) hEnn
  have hE1 : ∀ j : ℕ,
      cubeBesovDepthSeminorm Q (1 / 2) (2 : ℝ≥0∞) u.toH1Function.toFun j ≤
        weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E := by
    intro j
    have h := h1_depthSeminorm_half_le_dimensional_energy Q A b hb u.toH1Function j
    rw [← hE] at h
    exact h
  have hE2 : |cubeAverage Q u.toH1Function.toFun| ≤
      weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q * E := by
    have h := h10_average_le_dimensional_energy Q A b hb u
    rw [← hE] at h
    exact h
  have havg : cubeBesovScaleWeight (1 / 2) Q * |cubeAverage Q u.toH1Function.toFun| ≤
      weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E := by
    have hnn : 0 ≤ cubeBesovScaleWeight (1 / 2) Q :=
      cubeBesovScaleWeight_nonneg (1 / 2) Q
    have hw : cubeBesovScaleWeight (1 / 2) Q * cubeScaleFactor Q =
        cubeBesovScaleWeight (-1 / 2) Q := by
      rw [← cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor,
        cubeBesovScaleWeight_mul_eq_scaleWeight_add]
      norm_num
    calc cubeBesovScaleWeight (1 / 2) Q * |cubeAverage Q u.toH1Function.toFun| ≤
        cubeBesovScaleWeight (1 / 2) Q *
          (weightedLocalSobolevEnergyConstant d * cubeScaleFactor Q * E) :=
        mul_le_mul_of_nonneg_left hE2 hnn
      _ = weightedLocalSobolevEnergyConstant d *
            (cubeBesovScaleWeight (1 / 2) Q * cubeScaleFactor Q) * E := by ring
      _ = weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E := by
          rw [hw]
  have hconj2 : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hof : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) u.toH1Function.toFun := by
    intro j R hR
    have hp : MemLp u.toH1Function.toFun (ENNReal.ofReal (2 : ℝ))
        (normalizedCubeMeasure Q) := by
      rw [hof]
      exact h1_memLp_normalizedCubeMeasure Q u.toH1Function
    have h := cubeFluctuation_memLp_of_parent_memLp Q (2 : ℝ) hp j R hR
    rw [hof] at h
    rw [hconj2]
    exact h
  have hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q (1 / 2) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N u.toH1Function.toFun ≤
        2 * weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E := by
    intro N
    have hconj1 : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
      simp [cubeBesovConjExponent, ENNReal.conjExponent]
    have hsup : (Finset.range (N + 1)).sup' ⟨0, by simp⟩
        (fun j => cubeBesovDepthSeminorm Q (1 / 2) (2 : ℝ≥0∞) u.toH1Function.toFun j) ≤
        weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E := by
      refine Finset.sup'_le _ _ ?_
      intro j _
      exact hE1 j
    simp only [cubeBesovDualTestNorm, hconj1, hconj2, if_true, cubeBesovPartialNormTop,
      cubeBesovPartialSeminormTop, Real.norm_eq_abs]
    calc (Finset.range (N + 1)).sup' ⟨0, by simp⟩
          (fun j => cubeBesovDepthSeminorm Q (1 / 2) (2 : ℝ≥0∞) u.toH1Function.toFun j) +
        cubeBesovScaleWeight (1 / 2) Q * |cubeAverage Q u.toH1Function.toFun| ≤
        weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E +
          weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E :=
        add_le_add hsup havg
      _ = 2 * weightedLocalSobolevEnergyConstant d *
            cubeBesovScaleWeight (-1 / 2) Q * E := by ring
  calc |cubeAverage Q (fun x => g x * u.toH1Function.toFun x)|
      = |cubeBesovPairing Q g u.toH1Function.toFun| := rfl
    _ ≤ ((3 : ℝ) ^ ((d : ℝ) + 1 / 2) *
          cubeBesovCircNorm Q (1 / 2) (2 : ℝ≥0∞) (1 : ℝ≥0∞) g) *
        (2 * weightedLocalSobolevEnergyConstant d * cubeBesovScaleWeight (-1 / 2) Q * E) :=
      abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one_of_nonneg
        Q (1 / 2) g u.toH1Function.toFun (by norm_num : (0 : ℝ) < 1 / 2) hg hB hnorm hmem
    _ = (2 * (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * weightedLocalSobolevEnergyConstant d) *
        cubeBesovCircNorm Q (1 / 2) (2 : ℝ≥0∞) (1 : ℝ≥0∞) g *
        cubeBesovScaleWeight (-1 / 2) Q * E := by ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
