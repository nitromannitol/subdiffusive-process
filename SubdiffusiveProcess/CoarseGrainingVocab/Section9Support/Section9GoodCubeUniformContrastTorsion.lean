module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSmallContrastL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeScaledPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCoefficientNormalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionTest
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge
public import Homogenization.Sobolev.Foundations.CubePoisson.Solver
@[expose] public section

/-! An arbitrarily small local coefficient ratio gives the actual normalized weighted-torsion comparison on every integer triadic cube. -/

set_option autoImplicit false
open Homogenization MeasureTheory Set Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem exists_goodCube_uniformContrast_torsionComparison
    (d : ℕ) [NeZero d] (eps : ℝ) (heps : 0 < eps) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∀ (Q : TriadicCube d) (a : Vec d → ℝ) (k : ℝ), 0 < k →
        ContinuousOn a (openCubeSet Q) →
        (∀ x ∈ openCubeSet Q, k ≤ a x ∧ a x ≤ (1 + tau) * k) →
        GoodCubeTorsionComparisonTest Q a 1 eps
:= by
  obtain ⟨P, hP, hPoincare⟩ := exists_goodCube_scaled_zeroTrace_poincare d
  let tau : ℝ := min 1 (eps / (4 * P^2))
  have hden : 0 < 4 * P^2 := by positivity
  have htau : 0 < tau := lt_min zero_lt_one (div_pos heps hden)
  have htau1 : tau ≤ 1 := min_le_left _ _
  have htauE : 4 * P^2 * tau ≤ eps := by
    have hdiv := (le_div_iff₀ hden).mp (min_le_right (1 : ℝ) (eps / (4 * P^2)))
    nlinarith only [hdiv]
  refine ⟨tau, htau, htau1, ?_⟩
  intro Q a k hk ha hbound
  let b : Vec d → ℝ := fun x => a x / k
  have hQm : MeasurableSet (openCubeSet Q) := measurableSet_openCubeSet Q
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hR : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hbcont : ContinuousOn b (openCubeSet Q) := ha.div_const k
  have hb1 : ∀ x ∈ openCubeSet Q, 1 ≤ b x ∧ b x ≤ 1 + tau := by
    intro x hx
    exact ⟨(one_le_div₀ hk).2 (hbound x hx).1,
      (div_le_iff₀ hk).2 (hbound x hx).2⟩
  have hEll : IsEllipticFieldOn (1 / 2) 2 (openCubeSet Q) (scalarCoeffField b) :=
    Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
      hQm hbcont (by norm_num) (by
        intro x hx
        obtain ⟨h1, h2⟩ := hb1 x hx
        constructor <;> linarith only [h1, h2, htau1])
  have hbL2 : MemL2On (openCubeSet Q) b := by
    apply MemLp.of_bound (hbcont.aestronglyMeasurable hQm) 2
    filter_upwards [ae_restrict_mem hQm] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (hb1 x hx).1)]
    linarith only [(hb1 x hx).2, htau1]
  have hcontrast : ∀ x ∈ openCubeSet Q, |b x - 1| ≤ tau := by
    intro x hx
    rw [abs_of_nonneg (sub_nonneg.2 (hb1 x hx).1)]
    linarith only [(hb1 x hx).2]
  intro u w hu hw
  have huB : IsMassiveWeakSolutionOn b b 0 (openCubeSet Q)
      u.toH1Function (fun _ => 1) :=
    (goodCube_massiveWeakSolution_div_common_coefficient hk.ne' 0
      u.toH1Function (fun _ => 1)).mpr hu
  have hcmp := goodCube_weightedTorsion_l2_comparison_of_uniform_contrast
    hQm hEll hbL2 hcontrast htau.le (mul_nonneg hP.le hR.le)
    (hPoincare Q) u w huB hw
  have hn := norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two Q
    (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy.h1_memLp_normalizedCubeMeasure Q (u - w).toH1Function)
  have hn' : ‖(u - w).toH1Function.toScalarL2‖ =
      (cubeVolume Q)^(1 / 2 : ℝ) * cubeLpNorm Q 2 (u - w).toH1Function.toFun := hn
  rw [← Homogenization.l2_normSq_eq_integral (u - w).toH1Function,
    Real.sqrt_sq (norm_nonneg _), volume_openCubeSet_toReal, Real.sqrt_eq_rpow] at hcmp
  have hbudget : 4 * (P * cubeScaleFactor Q)^2 * tau ≤ eps * (cubeScaleFactor Q)^2 := by
    calc 4 * (P * cubeScaleFactor Q)^2 * tau
        = (4 * P^2 * tau) * (cubeScaleFactor Q)^2 := by ring
      _ ≤ eps * (cubeScaleFactor Q)^2 :=
        mul_le_mul_of_nonneg_right htauE (sq_nonneg _)
  have hvol : 0 < (cubeVolume Q)^(1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (cubeVolume_pos Q) _
  have hfull : (cubeVolume Q)^(1 / 2 : ℝ) *
      cubeLpNorm Q 2 (u - w).toH1Function.toFun ≤
      (cubeVolume Q)^(1 / 2 : ℝ) * (eps * (cubeScaleFactor Q)^2) := by
    calc _ = ‖(u - w).toH1Function.toScalarL2‖ := hn'.symm
      _ ≤ 4 * (P * cubeScaleFactor Q)^2 * tau * (cubeVolume Q)^(1 / 2 : ℝ) := hcmp
      _ ≤ (eps * (cubeScaleFactor Q)^2) * (cubeVolume Q)^(1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hbudget hvol.le
      _ = _ := by ring
  have hfun : (fun x => u.toH1Function.toFun x - w.toH1Function.toFun x) =
      (u - w).toH1Function.toFun := by
    funext x
    change u.toH1Function.toFun x - w.toH1Function.toFun x =
      u.toH1Function.toFun x + (-1) * w.toH1Function.toFun x
    ring
  rw [hfun, div_one]
  exact le_of_mul_le_mul_left hfull hvol

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
