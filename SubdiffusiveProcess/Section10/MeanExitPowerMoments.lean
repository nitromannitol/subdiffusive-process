module

public import SubdiffusiveProcess.Section10.KilledSobolevMoment

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- A deterministic positive factor and real power transport the literal
lower-integral moment. Its input order is e*Q, before any disorder threshold. -/
theorem lintegral_factor_power_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {K : Ω → ℝ} {D e Q C : ℝ}
    (_hK : Measurable K) (hK0 : ∀ omega, 0 ≤ K omega) (hD : 0 ≤ D)
    (hm : (∫⁻ omega, ENNReal.ofReal (K omega ^ (e * Q)) ∂P) ≤ ENNReal.ofReal C) :
    (∫⁻ omega, ENNReal.ofReal ((D * K omega ^ e) ^ Q) ∂P) ≤
      ENNReal.ofReal (D ^ Q * C) := by
  have heq (omega) : (D * K omega ^ e) ^ Q = D ^ Q * K omega ^ (e * Q) := by
    rw [Real.mul_rpow hD (Real.rpow_nonneg (hK0 omega) e),
      ← Real.rpow_mul (hK0 omega)]
  simp_rw [heq, ENNReal.ofReal_mul (Real.rpow_nonneg hD Q)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_right hm _

end SubdiffusiveProcess.Section10
