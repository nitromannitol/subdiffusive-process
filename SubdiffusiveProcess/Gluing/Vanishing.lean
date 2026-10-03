module

public import Mathlib

@[expose] public section

/-!
# Gluing: the boundary layer of a bounded cutoff family does not see a continuous function

If `S_n` are smooth cutoffs, `0 ≤ S_n ≤ 1`, `S_n → 1` on the open set `Ω`, and the `L¹` norms of
`∂_j S_n` stay bounded, then `∫ f ∂_j S_n → 0` for every continuous compactly supported `f`
that can be approximated uniformly by smooth compactly supported functions with support in `Ω`.
For a smooth approximant `ψ` the integral is `-∫ ∂_jψ S_n → -∫ ∂_jψ = 0`; the general case follows
from the uniform `L¹` bound.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ}

theorem gl_tsupport_fderiv_apply_subset {φ : (Fin d → ℝ) → ℝ} (v : Fin d → ℝ) :
    tsupport (fun x => (fderiv ℝ φ x) v) ⊆ tsupport φ := by
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro x hx
  by_contra hxs
  have hzero : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxs] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  have : fderiv ℝ φ x = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hzero]
    simp
  exact hx (by simp [this])

/-- The integral of a partial derivative of a compactly supported `C¹` function vanishes. -/
theorem integral_fderiv_apply_eq_zero' {ψ : (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (j : Fin d) : ∫ x, fderiv ℝ ψ x (Pi.single j 1) = 0 := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hcont : Continuous fun x => fderiv ℝ ψ x (Pi.single j 1) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport fun x => fderiv ℝ ψ x (Pi.single j 1) :=
    hψc.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
  have hint : Integrable fun x => fderiv ℝ ψ x (Pi.single j 1) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hψint : Integrable ψ := hd.continuous.integrable_of_hasCompactSupport hψc
  have key : ∫ x, ψ x * (fderiv ℝ (fun _ : Fin d → ℝ => (1 : ℝ)) x) (Pi.single j 1)
      = -∫ x, (fderiv ℝ ψ x) (Pi.single j 1) * (1 : ℝ) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (by simpa using hint) (by simp) (by simpa using hψint) (fun x _ => hd x) (fun x _ => differentiableAt_const (1 : ℝ))
  have h0 : (0 : ℝ) = -∫ x, (fderiv ℝ ψ x) (Pi.single j 1) := by simpa using key
  linarith [h0]

/-- Integration by parts against a smooth function, one of whose factors has compact support. -/
theorem integral_mul_fderiv_neg {ψ S : (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hS : ContDiff ℝ ∞ S) (j : Fin d) :
    ∫ x, ψ x * fderiv ℝ S x (Pi.single j 1) = -∫ x, fderiv ℝ ψ x (Pi.single j 1) * S x := by
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hdS : Differentiable ℝ S := hS.differentiable (by simp)
  have hcψ : Continuous ψ := hdψ.continuous
  have hcS : Continuous S := hdS.continuous
  have hcψ' : Continuous fun x => fderiv ℝ ψ x (Pi.single j 1) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcS' : Continuous fun x => fderiv ℝ S x (Pi.single j 1) :=
    (hS.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs' : HasCompactSupport fun x => fderiv ℝ ψ x (Pi.single j 1) :=
    hψc.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hcψ'.mul hcS).integrable_of_hasCompactSupport hcs'.mul_right)
    ((hcψ.mul hcS').integrable_of_hasCompactSupport hψc.mul_right)
    ((hcψ.mul hcS).integrable_of_hasCompactSupport hψc.mul_right)
    (fun x _ => hdψ x) (fun x _ => hdS x)

theorem tendsto_integral_mul_fderiv_zero {Ω : Set (Fin d → ℝ)} {S : ℕ → (Fin d → ℝ) → ℝ}
    (hS : ∀ n, ContDiff ℝ ∞ (S n)) (hSc : ∀ n, HasCompactSupport (S n))
    (hSlim : ∀ᵐ x, x ∈ Ω → Tendsto (fun n => S n x) atTop (𝓝 1))
    (hS01 : ∀ n x, 0 ≤ S n x ∧ S n x ≤ 1)
    (j : Fin d) {C : ℝ} (hC : ∀ n, ∫ x, |fderiv ℝ (S n) x (Pi.single j 1)| ≤ C)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ ψ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ω ∧ ∀ x, |f x - ψ x| ≤ ε) :
    Tendsto (fun n => ∫ x, f x * fderiv ℝ (S n) x (Pi.single j 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε₀ hε₀
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' + 1 := by linarith
  set ε : ℝ := ε₀ / (2 * (C' + 1)) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨ψ, hψ, hψc, hψΩ, hψf⟩ := happrox ε hεpos
  -- the limit for the smooth approximant
  have hψlim : Tendsto (fun n => ∫ x, ψ x * fderiv ℝ (S n) x (Pi.single j 1)) atTop (𝓝 0) := by
    have hcψ' : Continuous fun x => fderiv ℝ ψ x (Pi.single j 1) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs' : HasCompactSupport fun x => fderiv ℝ ψ x (Pi.single j 1) :=
      hψc.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
    have hint' : Integrable fun x => fderiv ℝ ψ x (Pi.single j 1) :=
      hcψ'.integrable_of_hasCompactSupport hcs'
    have hdom : Tendsto (fun n => ∫ x, fderiv ℝ ψ x (Pi.single j 1) * S n x) atTop
        (𝓝 (∫ x, fderiv ℝ ψ x (Pi.single j 1) * 1)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun x => ‖fderiv ℝ ψ x (Pi.single j 1)‖) (fun n => ?_) hint'.norm (fun n => ?_)
        (hSlim.mono fun x hxlim => ?_)
      · exact (hcψ'.mul (hS n).continuous).aestronglyMeasurable
      · refine Eventually.of_forall fun x => ?_
        rw [norm_mul]
        have h1 := hS01 n x
        rw [Real.norm_of_nonneg h1.1]
        calc ‖fderiv ℝ ψ x (Pi.single j 1)‖ * S n x ≤ ‖fderiv ℝ ψ x (Pi.single j 1)‖ * 1 :=
              mul_le_mul_of_nonneg_left h1.2 (norm_nonneg _)
          _ = _ := mul_one _
      · by_cases hx : x ∈ Ω
        · exact (hxlim hx).const_mul _
        · have : fderiv ℝ ψ x (Pi.single j 1) = 0 := by
            have hnot : x ∉ tsupport fun x => fderiv ℝ ψ x (Pi.single j 1) :=
              fun hxt => hx (hψΩ (gl_tsupport_fderiv_apply_subset _ hxt))
            simpa using image_eq_zero_of_notMem_tsupport hnot
          simp [this]
    have hzero : ∫ x, fderiv ℝ ψ x (Pi.single j 1) * (1 : ℝ) = 0 := by
      simpa using integral_fderiv_apply_eq_zero' hψ hψc j
    rw [hzero] at hdom
    have := hdom.neg
    rw [neg_zero] at this
    refine this.congr fun n => ?_
    rw [integral_mul_fderiv_neg hψ hψc (hS n) j]
  rcases (Metric.tendsto_atTop.1 hψlim (ε₀ / 2) (by positivity)) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  -- comparison of `f` and `ψ`
  have hcS' : Continuous fun x => fderiv ℝ (S n) x (Pi.single j 1) :=
    ((hS n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs' : HasCompactSupport fun x => fderiv ℝ (S n) x (Pi.single j 1) :=
    (hSc n).fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
  have hSint : Integrable fun x => fderiv ℝ (S n) x (Pi.single j 1) :=
    hcS'.integrable_of_hasCompactSupport hcs'
  have hfint : Integrable fun x => f x * fderiv ℝ (S n) x (Pi.single j 1) :=
    (hf.mul hcS').integrable_of_hasCompactSupport hfc.mul_right
  have hψint : Integrable fun x => ψ x * fderiv ℝ (S n) x (Pi.single j 1) :=
    ((hψ.continuous).mul hcS').integrable_of_hasCompactSupport hψc.mul_right
  have hdiff : |(∫ x, f x * fderiv ℝ (S n) x (Pi.single j 1)) -
      (∫ x, ψ x * fderiv ℝ (S n) x (Pi.single j 1))| ≤ ε * C' := by
    rw [← integral_sub hfint hψint]
    calc |∫ x, (f x * fderiv ℝ (S n) x (Pi.single j 1) - ψ x * fderiv ℝ (S n) x (Pi.single j 1))|
        ≤ ∫ x, |f x * fderiv ℝ (S n) x (Pi.single j 1) -
            ψ x * fderiv ℝ (S n) x (Pi.single j 1)| := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun x => f x * fderiv ℝ (S n) x (Pi.single j 1) -
              ψ x * fderiv ℝ (S n) x (Pi.single j 1))
      _ ≤ ∫ x, ε * |fderiv ℝ (S n) x (Pi.single j 1)| := by
          refine integral_mono (hfint.sub hψint).abs (hSint.abs.const_mul ε) fun x => ?_
          rw [← sub_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (hψf x) (abs_nonneg _)
      _ = ε * ∫ x, |fderiv ℝ (S n) x (Pi.single j 1)| := integral_const_mul _ _
      _ ≤ ε * C' := mul_le_mul_of_nonneg_left ((hC n).trans (le_max_left _ _)) hεpos.le
  have hεC : ε * C' ≤ ε₀ / 2 := by
    rw [hε]
    calc ε₀ / (2 * (C' + 1)) * C' ≤ ε₀ / (2 * (C' + 1)) * (C' + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε₀ / 2 := by field_simp
  calc |∫ x, f x * fderiv ℝ (S n) x (Pi.single j 1)|
      ≤ |∫ x, ψ x * fderiv ℝ (S n) x (Pi.single j 1)| +
        |(∫ x, f x * fderiv ℝ (S n) x (Pi.single j 1)) -
          (∫ x, ψ x * fderiv ℝ (S n) x (Pi.single j 1))| := by
        have := abs_add_le (∫ x, ψ x * fderiv ℝ (S n) x (Pi.single j 1))
          ((∫ x, f x * fderiv ℝ (S n) x (Pi.single j 1)) -
            (∫ x, ψ x * fderiv ℝ (S n) x (Pi.single j 1)))
        simpa using this
    _ < ε₀ / 2 + ε₀ / 2 := by linarith
    _ = ε₀ := by ring

end SubdiffusiveProcess.Gluing
