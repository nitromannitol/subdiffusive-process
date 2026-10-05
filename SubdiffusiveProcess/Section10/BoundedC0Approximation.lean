module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

/-! Compact continuous L¹ approximations that preserve the global bound.
Clipping an approximation to the range interval fixes zero and decreases
its error against every function already in that interval. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ZeroAtInfty CompactlySupported

namespace SubdiffusiveProcess.Section10

/-- Clipping to a symmetric interval decreases distance from its points. -/
theorem abs_sub_clip_le {F x y : ℝ} (hF : 0 ≤ F) (hx : |x| ≤ F) :
    |x - max (-F) (min F y)| ≤ |x - y| := by
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  by_cases hy : y ≤ F
  · rw [min_eq_right hy]
    by_cases hl : -F ≤ y
    · rw [max_eq_right hl]
    · have hyl : y < -F := lt_of_not_ge hl
      rw [max_eq_left hyl.le, abs_of_nonneg (by linarith : 0 ≤ x - -F),
        abs_of_nonneg (by linarith : 0 ≤ x - y)]
      linarith
  · have hyu : F < y := lt_of_not_ge hy
    rw [min_eq_left hyu.le, max_eq_right (by linarith : -F ≤ F),
      abs_of_nonpos (by linarith : x - F ≤ 0),
      abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith

/-- Every bounded measurable real function has arbitrarily accurate L¹
approximations in C₀ with the same pointwise bound, for any finite measure
on the canonical finite-dimensional state space. -/
theorem exists_bounded_c0_integral_sub_le {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    {F : ℝ} (hF : 0 ≤ F) (hbound : ∀ x, |f x| ≤ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C₀(Fin d → ℝ, ℝ), (∀ x, |g x| ≤ F) ∧
      (∫ x, |f x - g x| ∂μ) ≤ ε := by
  have hfint : Integrable f μ :=
    (integrable_const F).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  obtain ⟨g, hgcs, hgerr, hgcont, hgint⟩ :=
    hfint.exists_hasCompactSupport_integral_sub_le hε
  let clip : ℝ → ℝ := fun y => max (-F) (min F y)
  have hclip0 : clip 0 = 0 := by simp [clip, hF, neg_nonpos.mpr hF]
  have hcont : Continuous (fun x => clip (g x)) :=
    continuous_const.max (continuous_const.min hgcont)
  have hcs : HasCompactSupport (fun x => clip (g x)) :=
    hgcs.comp_left hclip0
  let k : C_c(Fin d → ℝ, ℝ) :=
    { toFun := fun x => clip (g x)
      continuous_toFun := hcont
      hasCompactSupport' := hcs }
  have hkbound : ∀ x, |k x| ≤ F := by
    intro x
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hkint : Integrable (fun x => |f x - k x|) μ := by
    apply (integrable_const (2 * F)).mono'
      (hf.sub hcont.measurable).aestronglyMeasurable.norm
    filter_upwards [] with x
    have hsum : |f x| + |k x| ≤ 2 * F := by linarith [hbound x, hkbound x]
    simpa only [Pi.sub_apply, norm_norm, Real.norm_eq_abs, abs_abs] using!
      (abs_sub (f x) (k x)).trans hsum
  refine ⟨(k : C₀(Fin d → ℝ, ℝ)), hkbound, ?_⟩
  calc
    (∫ x, |f x - k x| ∂μ) ≤ ∫ x, ‖f x - g x‖ ∂μ := by
      apply integral_mono hkint (hfint.sub hgint).norm
      intro x
      exact abs_sub_clip_le hF (hbound x)
    _ ≤ ε := hgerr

end SubdiffusiveProcess.Section10
