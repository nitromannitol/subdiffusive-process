import Mathlib

/-!
# Stampacchia: smooth `1`-Lipschitz approximation of a normal contraction

A normal contraction `T` (`T 0 = 0`, `1`-Lipschitz) is the uniform limit of smooth `1`-Lipschitz
functions `S n` with `S n 0 = 0`, `‖S n - T‖_∞ ≤ 2/(n+1)`, obtained by convolving with a normalized
bump of radius `1/(n+1)` and subtracting the value at `0`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff Convolution
noncomputable section
namespace SubdiffusiveProcess.Stampacchia

/-- The bump of outer radius `1/(n+1)`. -/
def bump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]; nlinarith⟩

theorem bump_rOut (n : ℕ) : (bump n).rOut = 1 / ((n : ℝ) + 1) := rfl

/-- The mollification `ρ_n ⋆ T`. -/
def moll (T : ℝ → ℝ) (n : ℕ) : ℝ → ℝ := ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] T)

theorem moll_apply (T : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    moll T n x = ∫ t, (bump n).normed volume t • T (x - t) := rfl

theorem moll_contDiff {T : ℝ → ℝ} (hT : Continuous T) (n : ℕ) : ContDiff ℝ ∞ (moll T n) :=
  (bump n).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (bump n).contDiff_normed hT.locallyIntegrable

theorem abs_moll_sub_le {T : ℝ → ℝ} (hlip : ∀ s t, |T s - T t| ≤ |s - t|) (n : ℕ) (x : ℝ) :
    |moll T n x - T x| ≤ 1 / ((n : ℝ) + 1) := by
  have hcont : Continuous T := by
    have : LipschitzWith 1 T := LipschitzWith.of_dist_le_mul fun s t => by
      simpa [Real.dist_eq] using hlip s t
    exact this.continuous
  have := ContDiffBump.dist_normed_convolution_le (μ := volume) (φ := bump n) (g := T) (x₀ := x)
    (ε := 1 / ((n : ℝ) + 1)) hcont.aestronglyMeasurable (fun y hy => by
      rw [Real.dist_eq]
      refine (hlip y x).trans ?_
      have := Metric.mem_ball.1 hy
      rw [Real.dist_eq, bump_rOut] at this
      exact this.le)
  rw [Real.dist_eq] at this
  exact this

theorem abs_moll_sub_moll_le {T : ℝ → ℝ} (hlip : ∀ s t, |T s - T t| ≤ |s - t|) (n : ℕ)
    (a b : ℝ) : |moll T n a - moll T n b| ≤ |a - b| := by
  have hcont : Continuous T := by
    have : LipschitzWith 1 T := LipschitzWith.of_dist_le_mul fun s t => by
      simpa [Real.dist_eq] using hlip s t
    exact this.continuous
  set ρ := (bump n).normed volume with hρ
  have hρnn : ∀ t, 0 ≤ ρ t := fun t => (bump n).nonneg_normed t
  have hρint : ∫ t, ρ t = 1 := (bump n).integral_normed
  have hρc : HasCompactSupport ρ := (bump n).hasCompactSupport_normed
  have hρcont : Continuous ρ := (bump n).continuous_normed
  have hρi : Integrable ρ := hρcont.integrable_of_hasCompactSupport hρc
  have hint : ∀ x, Integrable (fun t => ρ t • T (x - t)) := by
    intro x
    have hc : Continuous fun t => ρ t • T (x - t) :=
      hρcont.smul (hcont.comp (continuous_const.sub continuous_id))
    exact hc.integrable_of_hasCompactSupport hρc.smul_right
  rw [moll_apply, moll_apply, ← integral_sub (hint a) (hint b)]
  rw [← Real.norm_eq_abs]
  calc ‖∫ t, (ρ t • T (a - t) - ρ t • T (b - t))‖ ≤ ∫ t, ρ t * |a - b| := by
        refine norm_integral_le_of_norm_le (hρi.mul_const _) (Eventually.of_forall fun t => ?_)
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hρnn t), Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (hρnn t)
        refine (hlip _ _).trans (le_of_eq ?_)
        congr 1; ring
    _ = |a - b| := by rw [integral_mul_const, hρint, one_mul]

/-- **Smooth `1`-Lipschitz approximation of a normal contraction.** -/
theorem exists_smooth_approx (T : ℝ → ℝ) (h0 : T 0 = 0) (hlip : ∀ s t, |T s - T t| ≤ |s - t|) :
    ∃ S : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (S n)) ∧ (∀ n, S n 0 = 0) ∧
      (∀ n s t, |S n s - S n t| ≤ |s - t|) ∧
      (∀ n t, |S n t - T t| ≤ 2 / ((n : ℝ) + 1)) := by
  have hcont : Continuous T := by
    have : LipschitzWith 1 T := LipschitzWith.of_dist_le_mul fun s t => by
      simpa [Real.dist_eq] using hlip s t
    exact this.continuous
  refine ⟨fun n t => moll T n t - moll T n 0, fun n => ?_, fun n => by simp,
    fun n s t => ?_, fun n t => ?_⟩
  · exact (moll_contDiff hcont n).sub contDiff_const
  · simpa using abs_moll_sub_moll_le hlip n s t
  · have h1 := abs_moll_sub_le hlip n t
    have h2 := abs_moll_sub_le hlip n 0
    rw [h0, sub_zero] at h2
    calc |moll T n t - moll T n 0 - T t| = |(moll T n t - T t) - moll T n 0| := by ring_nf
      _ ≤ |moll T n t - T t| + |moll T n 0| := abs_sub _ _
      _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_le_add h1 h2
      _ = 2 / ((n : ℝ) + 1) := by ring

theorem abs_deriv_le_one {S : ℝ → ℝ} (h : ∀ s t, |S s - S t| ≤ |s - t|) (t : ℝ) :
    |deriv S t| ≤ 1 := by
  have : LipschitzWith 1 S := LipschitzWith.of_dist_le_mul fun s t => by
    simpa [Real.dist_eq] using h s t
  simpa using norm_deriv_le_of_lipschitz this (x₀ := t)

end SubdiffusiveProcess.Stampacchia
