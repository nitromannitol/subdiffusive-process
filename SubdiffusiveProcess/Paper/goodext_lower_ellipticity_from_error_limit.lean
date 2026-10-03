module

public import SubdiffusiveProcess.Paper.in_J
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! A bounded actual homogenization error gives an explicit lower coarse
ellipticity constant. This module proves no probabilistic error estimate. -/
open Filter MeasureTheory Set SubdiffusiveProcess
open scoped Topology ENNReal
noncomputable section
namespace Paper

/-- Error at most one makes the same reference a lower ellipticity bound up to factor five. -/
theorem aux_goodext_lower_ellipticity_from_error_limit_finite
    {d : ℕ} (I : in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (w : SpatialCoordinates d) (r' a0 s : ℝ)
    (ha0 : 0 < a0) (hs : s ∈ Ioc (0 : ℝ) 1)
    (herr : I.err z r hr a w r' a0 s 2 ≤ 1) :
    a0 / 5 ≤ I.lam z r hr a w r' s 2 := by
  have he0 := I.err_nonneg z r hr a w r' a0 s 2
  have hsquare : I.err z r hr a w r' a0 s 2 ^ 2 ≤ 1 := by
    nlinarith only [he0, herr]
  have hbound := (I.bound_ellipticities_by_error z r hr a w r' a0 ha0 s hs 2 (Or.inr rfl)).2
  have htwo : (2 : ℝ≥0∞) ≠ 1 := by norm_num
  rw [if_neg htwo] at hbound
  have hsmall : a0 * (I.lam z r hr a w r' s 2)⁻¹ ≤ 5 := by
    have hmax := (le_max_right _ _).trans hbound
    linarith only [hmax, hsquare, herr]
  have hlam := I.lam_pos z r hr a w r' s 2
  rw [← div_eq_mul_inv] at hsmall
  have hmul := (div_le_iff₀ hlam).mp hsmall
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr (by linarith only [hmul])

/-- A strictly subunit error limit supplies the lower ellipticity bound eventually along the same sequence. -/
theorem goodext_lower_ellipticity_from_error_limit
    {d : ℕ} (I : in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (e : ℝ) (he : e < 1)
    (hlim : Tendsto (fun n => I.err z r hr (a n) w r' (scale n) s 2) atTop (𝓝 e)) :
    ∀ᶠ n in atTop, scale n / 5 ≤ I.lam z r hr (a n) w r' s 2 := by
  filter_upwards [hlim.eventually (gt_mem_nhds he)] with n hn
  exact aux_goodext_lower_ellipticity_from_error_limit_finite I z r hr (a n) w r' (scale n) s
    (hscale n) hs hn.le

end Paper
