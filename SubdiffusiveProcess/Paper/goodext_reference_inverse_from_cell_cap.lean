module

public import SubdiffusiveProcess.Paper.goodext_coarse_ellipticity_order
public import SubdiffusiveProcess.Analysis.ReferenceInverseInMeasure

@[expose] public section

/-! The genuine coarse coefficient cap controls a limiting reference inverse on the upper-margin event.
No source-growth constant is used as a substitute for ellipticity. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal
noncomputable section
namespace Paper

/-- A represented lower inverse cap bounds the reference on the normalized upper-coefficient event. -/
theorem goodext_reference_inverse_from_cell_cap
    {d : ℕ} [NeZero d] (I : in_J d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → Ω → PositiveCoefficient (centeredCube z r hr))
    (sigma : ℝ) (hsigma : sigma ∈ Ioc (0 : ℝ) 1)
    (scale : ℕ → Ω → ℝ) (s ell K : Ω → ℝ) (eta cap : ℝ)
    (hs : ∀ᵐ ω ∂P, 0 < s ω ∧ Tendsto (fun n => scale n ω) atTop (𝓝 (s ω)))
    (hcap : ∀ᵐ ω ∂P, 0 ≤ K ω ∧ ∀ᶠ n in atTop,
      I.Lam z r hr (a n ω) z r sigma 2 +
        (I.lam z r hr (a n ω) z r sigma 2)⁻¹ ≤ K ω * r ^ (-eta))
    (hNorm : TendstoInMeasure P
      (fun n ω => I.Lam z r hr (a n ω) z r sigma 2 / scale n ω) atTop ell) :
    ∀ᵐ ω ∂P, ell ω ≤ cap → (s ω)⁻¹ ≤ (K ω * r ^ (-eta)) * cap := by
  apply ae_reference_inv_le_of_coefficient_limits P
    (fun n ω => I.lam z r hr (a n ω) z r sigma 2)
    (fun n ω => I.Lam z r hr (a n ω) z r sigma 2)
    scale s ell (fun ω => K ω * r ^ (-eta)) cap ?_ hNorm
  filter_upwards [hs, hcap] with ω hω hk
  refine ⟨fun n => I.lam_pos _ _ _ _ _ _ _ _, ?_, ?_,
    mul_nonneg hk.1 (Real.rpow_nonneg hr.le _), hω.1, hω.2⟩
  · intro n
    exact goodext_coarse_ellipticity_order I z r hr (a n ω) z r hr Subset.rfl sigma hsigma
  · filter_upwards [hk.2] with n hn
    exact (le_add_of_nonneg_left (I.Lam_pos _ _ _ _ _ _ _ _).le).trans hn

end Paper
