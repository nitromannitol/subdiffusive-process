module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-! This module proves a scalar inverse-limit bound from coefficient order and an eventual
inverse cap. It does not claim a coefficient limit or a source-growth estimate. -/

open Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A lower-coefficient inverse cap and the normalized upper limit control the limiting reference inverse. -/
theorem reference_inv_le_of_coefficient_limits
    (lower upper scale : ℕ → ℝ) (s ell K C : ℝ)
    (hlower : ∀ n, 0 < lower n) (horder : ∀ n, lower n ≤ upper n)
    (hcap : ∀ᶠ n in atTop, (lower n)⁻¹ ≤ K)
    (hK : 0 ≤ K) (hs : 0 < s) (hell : ell ≤ C)
    (hScale : Tendsto scale atTop (𝓝 s))
    (hNorm : Tendsto (fun n => upper n / scale n) atTop (𝓝 ell)) :
    s⁻¹ ≤ K * C := by
  have hscale_pos : ∀ᶠ n in atTop, 0 < scale n :=
    hScale.eventually (Ioi_mem_nhds hs)
  have hInvOrder : ∀ᶠ n in atTop,
      (scale n)⁻¹ ≤ K * (upper n / scale n) := by
    filter_upwards [hscale_pos, hcap] with n hsn hcn
    have hup : 0 < upper n := lt_of_lt_of_le (hlower n) (horder n)
    have hupInv : (upper n)⁻¹ ≤ K := by
      exact (inv_anti₀ (hlower n) (horder n)).trans hcn
    calc
      (scale n)⁻¹ = (upper n)⁻¹ * (upper n / scale n) := by
        rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hup.ne', one_mul]
      _ ≤ K * (upper n / scale n) :=
        mul_le_mul_of_nonneg_right hupInv (div_nonneg hup.le hsn.le)
  have hScaleInv : Tendsto (fun n => (scale n)⁻¹) atTop (𝓝 (s⁻¹)) :=
    hScale.inv₀ hs.ne'
  have hProduct : Tendsto (fun n => K * (upper n / scale n)) atTop (𝓝 (K * ell)) :=
    tendsto_const_nhds.mul hNorm
  have hlimit : s⁻¹ ≤ K * ell :=
    le_of_tendsto_of_tendsto hScaleInv hProduct hInvOrder
  exact hlimit.trans (mul_le_mul_of_nonneg_left hell hK)

end SubdiffusiveProcess
