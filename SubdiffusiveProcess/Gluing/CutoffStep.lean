import Mathlib

/-!
# Gluing: the one-dimensional smooth step and its derivative bounds
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
namespace SubdiffusiveProcess.Gluing

/-- The derivative of `Real.smoothTransition` vanishes outside `(0,1)`. -/
theorem deriv_st_eq_zero {s : ℝ} (h : s ≤ 0 ∨ 1 ≤ s) : deriv Real.smoothTransition s = 0 := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.1 Real.smoothTransition.contDiff).2.continuous
  have hleft : ∀ s < 0, deriv Real.smoothTransition s = 0 := by
    intro s hs
    have hev : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with u hu
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hu)
    rw [Filter.EventuallyEq.deriv_eq hev]; simp
  have hright : ∀ s > 1, deriv Real.smoothTransition s = 0 := by
    intro s hs
    have hev : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with u hu
      exact Real.smoothTransition.one_of_one_le (le_of_lt hu)
    rw [Filter.EventuallyEq.deriv_eq hev]; simp
  rcases h with h | h
  · have hsub : Iio (0 : ℝ) ⊆ {s | deriv Real.smoothTransition s = 0} := fun s hs => hleft s hs
    have := closure_minimal hsub (isClosed_eq hc continuous_const)
    rw [closure_Iio] at this
    exact this h
  · have hsub : Ioi (1 : ℝ) ⊆ {s | deriv Real.smoothTransition s = 0} := fun s hs => hright s hs
    have := closure_minimal hsub (isClosed_eq hc continuous_const)
    rw [closure_Ioi] at this
    exact this h

/-- A uniform bound on the derivative of `Real.smoothTransition`. -/
theorem exists_deriv_st_bound : ∃ T : ℝ, 0 ≤ T ∧ ∀ s, |deriv Real.smoothTransition s| ≤ T := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.1 Real.smoothTransition.contDiff).2.continuous
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    intro s hs
    simp only [mem_Icc, not_and_or, not_le] at hs
    exact deriv_st_eq_zero (by rcases hs with h | h <;> [left; right] <;> linarith)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  have := hC s
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- The one-dimensional cutoff of `(α, β)` with transition width `ε`: it vanishes for
`t ≤ α + ε` and `t ≥ β - ε` and equals `1` on `[α + 2ε, β - 2ε]`. -/
def gcEta (α β ε t : ℝ) : ℝ :=
  Real.smoothTransition ((t - α) / ε - 1) * Real.smoothTransition ((β - t) / ε - 1)

theorem gcEta_contDiff (α β ε : ℝ) : ContDiff ℝ ∞ (gcEta α β ε) := by
  unfold gcEta
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem gcEta_nonneg (α β ε t : ℝ) : 0 ≤ gcEta α β ε t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem gcEta_le_one (α β ε t : ℝ) : gcEta α β ε t ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem gcEta_eq_zero_of_le {α β ε t : ℝ} (hε : 0 < ε) (h : t ≤ α + ε) : gcEta α β ε t = 0 := by
  unfold gcEta
  rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
  rw [sub_nonpos, div_le_one hε]
  linarith

theorem gcEta_eq_zero_of_ge {α β ε t : ℝ} (hε : 0 < ε) (h : β - ε ≤ t) : gcEta α β ε t = 0 := by
  unfold gcEta
  exact mul_eq_zero_of_right _
    (Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one hε]; linarith))

theorem gcEta_eq_one {α β ε t : ℝ} (hε : 0 < ε) (h1 : α + 2 * ε ≤ t) (h2 : t ≤ β - 2 * ε) :
    gcEta α β ε t = 1 := by
  unfold gcEta
  rw [Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hε]; linarith),
    Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hε]; linarith),
    one_mul]

theorem gcEta_ne_zero_imp {α β ε t : ℝ} (hε : 0 < ε) (h : gcEta α β ε t ≠ 0) :
    α + ε < t ∧ t < β - ε := by
  constructor
  · by_contra hc
    exact h (gcEta_eq_zero_of_le hε (not_lt.1 hc))
  · by_contra hc
    exact h (gcEta_eq_zero_of_ge hε (not_lt.1 hc))

/-- The two summands of the derivative of `gcEta`. -/
theorem hasDerivAt_gcEta (α β ε t : ℝ) (hε : 0 < ε) :
    HasDerivAt (gcEta α β ε)
      (deriv Real.smoothTransition ((t - α) / ε - 1) / ε *
          Real.smoothTransition ((β - t) / ε - 1) -
        Real.smoothTransition ((t - α) / ε - 1) *
          (deriv Real.smoothTransition ((β - t) / ε - 1) / ε)) t := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    Real.smoothTransition.contDiff.differentiable le_rfl
  have hst : ∀ s, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s := fun s =>
    (hd s).hasDerivAt
  have hA : HasDerivAt (fun t : ℝ => (t - α) / ε - 1) (1 / ε) t := by
    have := ((hasDerivAt_id t).sub_const α).div_const ε |>.sub_const 1
    simpa using this
  have hB : HasDerivAt (fun t : ℝ => (β - t) / ε - 1) (-1 / ε) t := by
    have := ((hasDerivAt_id t).const_sub β).div_const ε |>.sub_const 1
    simpa using this
  have h1 := (hst ((t - α) / ε - 1)).comp t hA
  have h2 := (hst ((β - t) / ε - 1)).comp t hB
  have hm := h1.mul h2
  have hfun : gcEta α β ε = (Real.smoothTransition ∘ fun t : ℝ => (t - α) / ε - 1) *
      (Real.smoothTransition ∘ fun t : ℝ => (β - t) / ε - 1) := by
    funext t; rfl
  rw [hfun]
  refine hm.congr_deriv ?_
  simp only [Function.comp_apply]
  ring

end SubdiffusiveProcess.Gluing
