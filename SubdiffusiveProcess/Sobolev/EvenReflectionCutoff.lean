module

public import SubdiffusiveProcess.Geometry.ReflectionCalculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# One-sided smooth cutoffs away from a coordinate plane

`evenReflectionStep` equals `1` on `(-∞, -2]`, `0` on `[-1, ∞)`, and is
smooth with values in `[0, 1]`; it is built from `Real.smoothTransition`.
Rescaling by `ε` gives a cutoff vanishing within distance `ε` of the plane
`{x i = z i}` on the upper side and equal to `1` at distance `2ε` on the
lower side. The derivative bound `C / ε` and the localization of the
derivative to the strip `-2ε ≤ t ≤ -ε` are proved explicitly; they are the
only quantitative inputs of the interface test lemma.
-/

open Filter Set
open scoped ContDiff Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- One-sided unit step: `1` for `t ≤ -2`, `0` for `t ≥ -1`. -/
def evenReflectionStep (t : ℝ) : ℝ := Real.smoothTransition (-t - 1)

theorem evenReflectionStep_contDiff : ContDiff ℝ ∞ evenReflectionStep :=
  Real.smoothTransition.contDiff.comp (contDiff_id.neg.sub contDiff_const)

theorem evenReflectionStep_nonneg (t : ℝ) : 0 ≤ evenReflectionStep t :=
  Real.smoothTransition.nonneg _

theorem evenReflectionStep_le_one (t : ℝ) : evenReflectionStep t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem evenReflectionStep_eq_zero {t : ℝ} (ht : -1 ≤ t) : evenReflectionStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem evenReflectionStep_eq_one {t : ℝ} (ht : t ≤ -2) : evenReflectionStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The step is locally constant outside `[-2, -1]`. -/
theorem deriv_evenReflectionStep_eq_zero {t : ℝ} (ht : t < -2 ∨ -1 < t) :
    deriv evenReflectionStep t = 0 := by
  rcases ht with ht | ht
  · have h : evenReflectionStep =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact evenReflectionStep_eq_one (le_of_lt hs)
    rw [h.deriv_eq, deriv_const]
  · have h : evenReflectionStep =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact evenReflectionStep_eq_zero (le_of_lt hs)
    rw [h.deriv_eq, deriv_const]

theorem hasCompactSupport_deriv_evenReflectionStep :
    HasCompactSupport (deriv evenReflectionStep) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-2 : ℝ)) (b := -1))
  intro t ht
  by_contra h
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  exact ht (deriv_evenReflectionStep_eq_zero h)

/-- A uniform bound for the derivative of the unit step. -/
theorem exists_bound_deriv_evenReflectionStep :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv evenReflectionStep t| ≤ C := by
  obtain ⟨C, hC⟩ := hasCompactSupport_deriv_evenReflectionStep.exists_bound_of_continuous
    (evenReflectionStep_contDiff.continuous_deriv (by simp))
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun t => ?_⟩
  simpa only [Real.norm_eq_abs] using hC t

/-- The step rescaled to transition on `[-2ε, -ε]`. -/
def evenReflectionCutoff (ε t : ℝ) : ℝ := evenReflectionStep (t / ε)

theorem evenReflectionCutoff_contDiff (ε : ℝ) : ContDiff ℝ ∞ (evenReflectionCutoff ε) :=
  evenReflectionStep_contDiff.comp (contDiff_id.div_const ε)

theorem evenReflectionCutoff_nonneg (ε t : ℝ) : 0 ≤ evenReflectionCutoff ε t :=
  evenReflectionStep_nonneg _

theorem evenReflectionCutoff_le_one (ε t : ℝ) : evenReflectionCutoff ε t ≤ 1 :=
  evenReflectionStep_le_one _

theorem evenReflectionCutoff_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : -ε ≤ t) :
    evenReflectionCutoff ε t = 0 :=
  evenReflectionStep_eq_zero (by rw [le_div_iff₀ hε]; linarith)

theorem evenReflectionCutoff_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -(2 * ε)) :
    evenReflectionCutoff ε t = 1 :=
  evenReflectionStep_eq_one (by rw [div_le_iff₀ hε]; linarith)

theorem evenReflectionCutoff_hasDerivAt (ε t : ℝ) :
    HasDerivAt (evenReflectionCutoff ε) (deriv evenReflectionStep (t / ε) * (1 / ε)) t :=
  ((evenReflectionStep_contDiff.differentiable (by simp)) (t / ε)).hasDerivAt.comp t
    ((hasDerivAt_id t).div_const ε)

theorem deriv_evenReflectionCutoff (ε t : ℝ) :
    deriv (evenReflectionCutoff ε) t = deriv evenReflectionStep (t / ε) * (1 / ε) :=
  (evenReflectionCutoff_hasDerivAt ε t).deriv

/-- The rescaled derivative vanishes outside the strip `-2ε ≤ t ≤ -ε`. -/
theorem deriv_evenReflectionCutoff_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t < -(2 * ε) ∨ -ε < t) :
    deriv (evenReflectionCutoff ε) t = 0 := by
  rw [deriv_evenReflectionCutoff, deriv_evenReflectionStep_eq_zero, zero_mul]
  rcases ht with ht | ht
  · left
    rw [div_lt_iff₀ hε]
    linarith
  · right
    rw [lt_div_iff₀ hε]
    linarith

/-- The rescaled derivative is bounded by `C / ε`. -/
theorem abs_deriv_evenReflectionCutoff_le {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hC : ∀ s, |deriv evenReflectionStep s| ≤ C) (t : ℝ) :
    |deriv (evenReflectionCutoff ε) t| ≤ C / ε := by
  rw [deriv_evenReflectionCutoff, abs_mul, abs_of_pos (one_div_pos.mpr hε), div_eq_mul_one_div C ε]
  exact mul_le_mul_of_nonneg_right (hC _) (one_div_pos.mpr hε).le

/-- The spatial cutoff depending only on the reflected coordinate. -/
def evenReflectionSpatialCutoff (z : SpatialCoordinates d) (i : Fin d) (ε : ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  evenReflectionCutoff ε (x i - z i)

theorem evenReflectionSpatialCutoff_contDiff (z : SpatialCoordinates d) (i : Fin d) (ε : ℝ) :
    ContDiff ℝ ∞ (evenReflectionSpatialCutoff z i ε) :=
  (evenReflectionCutoff_contDiff ε).comp ((contDiff_apply ℝ ℝ i).sub contDiff_const)

theorem evenReflectionSpatialCutoff_nonneg (z : SpatialCoordinates d) (i : Fin d) (ε : ℝ)
    (x : SpatialCoordinates d) : 0 ≤ evenReflectionSpatialCutoff z i ε x :=
  evenReflectionCutoff_nonneg _ _

theorem evenReflectionSpatialCutoff_le_one (z : SpatialCoordinates d) (i : Fin d) (ε : ℝ)
    (x : SpatialCoordinates d) : evenReflectionSpatialCutoff z i ε x ≤ 1 :=
  evenReflectionCutoff_le_one _ _

theorem evenReflectionSpatialCutoff_eq_zero (z : SpatialCoordinates d) (i : Fin d) {ε : ℝ}
    (hε : 0 < ε) {x : SpatialCoordinates d} (hx : z i - ε ≤ x i) :
    evenReflectionSpatialCutoff z i ε x = 0 :=
  evenReflectionCutoff_eq_zero hε (by linarith)

theorem evenReflectionSpatialCutoff_eq_one (z : SpatialCoordinates d) (i : Fin d) {ε : ℝ}
    (hε : 0 < ε) {x : SpatialCoordinates d} (hx : x i ≤ z i - 2 * ε) :
    evenReflectionSpatialCutoff z i ε x = 1 :=
  evenReflectionCutoff_eq_one hε (by linarith)

theorem evenReflectionSpatialCutoff_hasFDerivAt (z : SpatialCoordinates d) (i : Fin d) (ε : ℝ)
    (x : SpatialCoordinates d) :
    HasFDerivAt (evenReflectionSpatialCutoff z i ε)
      (deriv (evenReflectionCutoff ε) (x i - z i) •
        (ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ)) x :=
  (((evenReflectionCutoff_contDiff ε).differentiable (by simp)) (x i - z i)).hasDerivAt.comp_hasFDerivAt
    x ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin d => ℝ) i x).sub_const (z i))

/-- Only the reflected coordinate derivative of the spatial cutoff is nonzero. -/
theorem fderiv_evenReflectionSpatialCutoff_single (z : SpatialCoordinates d) (i : Fin d) (ε : ℝ)
    (x : SpatialCoordinates d) (j : Fin d) :
    fderiv ℝ (evenReflectionSpatialCutoff z i ε) x (Pi.single j 1) =
      if j = i then deriv (evenReflectionCutoff ε) (x i - z i) else 0 := by
  rw [(evenReflectionSpatialCutoff_hasFDerivAt z i ε x).fderiv, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- The cutoff scales used along the interface limit. -/
def evenReflectionScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem evenReflectionScale_pos (n : ℕ) : 0 < evenReflectionScale n :=
  one_div_pos.mpr (by positivity)

theorem evenReflectionScale_tendsto : Tendsto evenReflectionScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Strictly below the plane, the cutoff eventually equals one. -/
theorem eventually_evenReflectionSpatialCutoff_eq_one (z : SpatialCoordinates d) (i : Fin d)
    {x : SpatialCoordinates d} (hx : x i < z i) :
    ∀ᶠ n in atTop, evenReflectionSpatialCutoff z i (evenReflectionScale n) x = 1 := by
  filter_upwards [(tendsto_order.1 evenReflectionScale_tendsto).2 ((z i - x i) / 2)
    (by linarith)] with n hn
  exact evenReflectionSpatialCutoff_eq_one z i (evenReflectionScale_pos n) (by linarith)

/-- Strictly below the plane, the cutoff derivative eventually vanishes. -/
theorem eventually_deriv_evenReflectionCutoff_eq_zero (z : SpatialCoordinates d) (i : Fin d)
    {x : SpatialCoordinates d} (hx : x i < z i) :
    ∀ᶠ n in atTop, deriv (evenReflectionCutoff (evenReflectionScale n)) (x i - z i) = 0 := by
  filter_upwards [(tendsto_order.1 evenReflectionScale_tendsto).2 ((z i - x i) / 2)
    (by linarith)] with n hn
  exact deriv_evenReflectionCutoff_eq_zero (evenReflectionScale_pos n) (Or.inl (by linarith))

end SubdiffusiveProcess
end
