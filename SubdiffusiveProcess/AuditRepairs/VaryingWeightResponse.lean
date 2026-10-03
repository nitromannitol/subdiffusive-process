module

public import SubdiffusiveProcess.Sobolev.ResponseComparison
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-! Uniform approximation of logarithmic weights preserves limits of actual inverse responses. -/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.AuditRepairs

/-- Compact-open convergence supplies a measurable norm error for each fixed compact cube. -/
theorem exists_compact_log_error
    {X : Type*} [TopologicalSpace X] (K : Set X) [CompactSpace K]
    (ellN : ℕ → C(X, ℝ)) (ell : C(X, ℝ))
    (h : Tendsto ellN atTop (𝓝 ell)) :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ Tendsto D atTop (𝓝 0) ∧
      ∀ n x, x ∈ K → |ellN n x - ell x| ≤ D n := by
  let D : ℕ → ℝ := fun n => ‖(ellN n).restrict K - ell.restrict K‖
  have hr : Tendsto (fun n => (ellN n).restrict K) atTop (𝓝 (ell.restrict K)) :=
    ((ContinuousMap.continuous_restrict K).tendsto ell).comp h
  refine ⟨D, fun n => norm_nonneg _, ?_, ?_⟩
  · simpa only [sub_self, norm_zero] using
      (hr.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => ell.restrict K)
        atTop (𝓝 (ell.restrict K)))).norm
  · intro n x hx
    simpa only [ContinuousMap.sub_apply, ContinuousMap.restrict_apply, Real.norm_eq_abs] using
      (ContinuousMap.norm_coe_le_norm ((ellN n).restrict K - ell.restrict K) ⟨x, hx⟩)

/-- The exact exponential coefficient comparison absorbs a vanishing log-weight error. -/
theorem inverse_response_tendsto_of_exp_comparison
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) (S : ResponseSpace Q)
    (a b : ℕ → PositiveCoefficient Q) (L : S.space →L[ℝ] ℝ)
    (D : ℕ → ℝ) (hD : Tendsto D atTop (𝓝 0))
    (hl : ∀ n, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      Real.exp (-D n) * (a n).val x ≤ (b n).val x)
    (hu : ∀ n, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (b n).val x ≤ Real.exp (D n) * (a n).val x)
    (R : ℝ) (hR : Tendsto (fun n => inverseResponse S (a n) L) atTop (𝓝 R)) :
    Tendsto (fun n => inverseResponse S (b n) L) atTop (𝓝 R) := by
  have hlo : Tendsto (fun n => Real.exp (-D n) * inverseResponse S (a n) L)
      atTop (𝓝 R) := by
    simpa using ((Real.continuous_exp.tendsto (-0)).comp hD.neg).mul hR
  have hhi : Tendsto (fun n => Real.exp (D n) * inverseResponse S (a n) L)
      atTop (𝓝 R) := by
    simpa using ((Real.continuous_exp.tendsto 0).comp hD).mul hR
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun n => (inverseResponse_exp_comparison S (a n) (b n) L (D n) (hl n) (hu n)).1)
    (fun n => (inverseResponse_exp_comparison S (a n) (b n) L (D n) (hl n) (hu n)).2)

/-- Literal weights on one common cutoff family give the required comparison. -/
theorem inverse_response_tendsto_of_log_weights
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) (S : ResponseSpace Q)
    (c a b : ℕ → PositiveCoefficient Q) (L : S.space →L[ℝ] ℝ)
    (ell : SpatialCoordinates d → ℝ) (ellN : ℕ → SpatialCoordinates d → ℝ)
    (ha : ∀ n, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (a n).val x = Real.exp (-ell x) * (c n).val x)
    (hb : ∀ n, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (b n).val x = Real.exp (-ellN n x) * (c n).val x)
    (D : ℕ → ℝ) (hD : Tendsto D atTop (𝓝 0))
    (hdiff : ∀ n, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      |ellN n x - ell x| ≤ D n)
    (R : ℝ) (hR : Tendsto (fun n => inverseResponse S (a n) L) atTop (𝓝 R)) :
    Tendsto (fun n => inverseResponse S (b n) L) atTop (𝓝 R) := by
  apply inverse_response_tendsto_of_exp_comparison Q S a b L D hD ?_ ?_ R hR
  · intro n
    obtain ⟨c0, hc0, hc⟩ := (c n).property
    filter_upwards [ha n, hb n, hdiff n, hc] with x hax hbx hdx hcx
    rw [hax, hbx, ← mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hdx).2])) (hc0.le.trans hcx)
  · intro n
    obtain ⟨c0, hc0, hc⟩ := (c n).property
    filter_upwards [ha n, hb n, hdiff n, hc] with x hax hbx hdx hcx
    rw [hax, hbx, ← mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hdx).1])) (hc0.le.trans hcx)

end SubdiffusiveProcess.AuditRepairs
