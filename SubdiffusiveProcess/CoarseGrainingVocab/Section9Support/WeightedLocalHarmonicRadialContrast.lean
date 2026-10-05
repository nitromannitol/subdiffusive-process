module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadialProfile
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadialGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicCoefficientControl
@[expose] public section




set_option autoImplicit false
open Homogenization hiding cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadial
theorem radial_contrast_forces_scale_bound {R kappa : ℝ} (hR : 3 < R)
    (hc : CoefficientContrastOn radialCoefficient kappa (radialOuter R)) :
    R ^ 2 ≤ 16 * kappa := by
  have hx : (![1 + R / 2, 10 * R ^ 2] : Vec 2) ∈ cubeSet (radialOuter R) := by
    rw [mem_radialOuter]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hy : (![2, 10 * R ^ 2] : Vec 2) ∈ cubeSet (radialOuter R) := by
    rw [mem_radialOuter]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨⟨by norm_num, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hax : radialCoefficient (![1 + R / 2, 10 * R ^ 2]) = (1 + R / 2) ^ 2 := by
    simp only [radialCoefficient, Matrix.cons_val_zero]
    rw [max_eq_right (by linarith : (1:ℝ) ≤ 1 + R / 2)]
  have hay : radialCoefficient (![2, 10 * R ^ 2]) = 4 := by
    norm_num [radialCoefficient, Matrix.cons_val_zero]
  have h := hc.2 _ hx _ hy
  rw [hax, hay] at h
  nlinarith

theorem not_uniform_radial_contrast (kappa : ℝ) :
    ¬ (∀ n : ℕ, 3 < (3:ℝ)^n →
      CoefficientContrastOn radialCoefficient kappa (radialOuter ((3:ℝ)^n))) := by
  intro h
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (max 4 (16 * abs kappa + 1)) (by norm_num : (1:ℝ) < 3)
  have hmax1 : (4:ℝ) ≤ max 4 (16 * abs kappa + 1) := le_max_left _ _
  have hmax2 : (16:ℝ) * abs kappa + 1 ≤ max 4 (16 * abs kappa + 1) := le_max_right _ _
  have h3n : 3 < (3:ℝ)^n := by linarith
  have hc := h n h3n
  have h1 := radial_contrast_forces_scale_bound h3n hc
  have hkle : (16:ℝ) * kappa ≤ 16 * abs kappa :=
    mul_le_mul_of_nonneg_left (le_abs_self kappa) (by norm_num)
  have h2 : (16:ℝ) * kappa < (3:ℝ)^n := by linarith
  have hpos : 0 < (3:ℝ)^n := by linarith
  have hsq : ((3:ℝ)^n) ^ 2 < (3:ℝ)^n := by linarith
  have hA : (3:ℝ) * (3:ℝ)^n < ((3:ℝ)^n) ^ 2 := by nlinarith [h3n, hpos]
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadial
