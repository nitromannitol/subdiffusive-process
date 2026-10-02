import Mathlib

/-! Fatou's lemma for the positive and the reciprocal moments of an almost surely convergent
sequence of positive random variables with uniformly bounded moments: the limit is almost surely
positive and inherits both bounds. Pure measure theory; no model input. -/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper
noncomputable section

/-- The `p`th power of the `L^p` norm is the lower integral of the `p`th power. -/
theorem aux_lem_response_reciprocal_fatou_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.2 hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hp

/-- Fatou for the positive and reciprocal moments: an almost sure limit of positive random
variables with uniformly bounded `L^p` norms of the variables and of their reciprocals is almost
surely positive and has the same two bounds. -/
theorem lem_response_reciprocal_fatou {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p C : ℝ) (hp : 0 < p) (Y : ℕ → Ω → ℝ) (Y0 : Ω → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hpos : ∀ n, ∀ᵐ ω ∂μ, 0 < Y n ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω)))
    (hup : ∀ n, eLpNorm (Y n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C)
    (hlow : ∀ n, eLpNorm (fun ω => (Y n ω)⁻¹) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    (∀ᵐ ω ∂μ, 0 < Y0 ω) ∧
      (MemLp Y0 (ENNReal.ofReal p) μ ∧ eLpNorm Y0 (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) ∧
      (MemLp (fun ω => (Y0 ω)⁻¹) (ENNReal.ofReal p) μ ∧
        eLpNorm (fun ω => (Y0 ω)⁻¹) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) := by
  have hY0 : AEStronglyMeasurable Y0 μ := aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  have hupper : eLpNorm Y0 (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas Y0 hlim).trans
      ((liminf_le_liminf (Eventually.of_forall hup)).trans_eq (liminf_const _))
  have hg : ∀ n, AEMeasurable (fun ω => (ENNReal.ofReal (Y n ω))⁻¹ ^ p) μ := fun n =>
    ((ENNReal.measurable_ofReal.comp_aemeasurable (hmeas n).aemeasurable).inv).pow_const p
  have hg0 : AEMeasurable (fun ω => (ENNReal.ofReal (Y0 ω))⁻¹ ^ p) μ :=
    ((ENNReal.measurable_ofReal.comp_aemeasurable hY0.aemeasurable).inv).pow_const p
  have hlint : ∀ n, ∫⁻ ω, (ENNReal.ofReal (Y n ω))⁻¹ ^ p ∂μ ≤ ENNReal.ofReal C ^ p := by
    intro n
    have h1 : ∫⁻ ω, (ENNReal.ofReal (Y n ω))⁻¹ ^ p ∂μ = ∫⁻ ω, ‖(Y n ω)⁻¹‖ₑ ^ p ∂μ := by
      refine lintegral_congr_ae ((hpos n).mono fun ω h => ?_)
      show (ENNReal.ofReal (Y n ω))⁻¹ ^ p = ‖(Y n ω)⁻¹‖ₑ ^ p
      rw [Real.enorm_eq_ofReal (inv_nonneg.2 h.le), ENNReal.ofReal_inv_of_pos h]
    rw [h1, aux_lem_response_reciprocal_fatou_lintegral μ _ hp]
    exact ENNReal.rpow_le_rpow (hlow n) hp.le
  have hfat : ∫⁻ ω, (ENNReal.ofReal (Y0 ω))⁻¹ ^ p ∂μ ≤ ENNReal.ofReal C ^ p := by
    calc ∫⁻ ω, (ENNReal.ofReal (Y0 ω))⁻¹ ^ p ∂μ
        = ∫⁻ ω, liminf (fun n => (ENNReal.ofReal (Y n ω))⁻¹ ^ p) atTop ∂μ := by
          refine lintegral_congr_ae (hlim.mono fun ω h => ?_)
          have ht : Tendsto (fun n => (ENNReal.ofReal (Y n ω))⁻¹ ^ p) atTop
              (𝓝 ((ENNReal.ofReal (Y0 ω))⁻¹ ^ p)) :=
            (ENNReal.continuous_rpow_const.tendsto _).comp
              (ENNReal.tendsto_inv_iff.2 (ENNReal.tendsto_ofReal h))
          exact ht.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, (ENNReal.ofReal (Y n ω))⁻¹ ^ p ∂μ) atTop :=
          lintegral_liminf_le' hg
      _ ≤ ENNReal.ofReal C ^ p :=
          (liminf_le_liminf (Eventually.of_forall hlint)).trans_eq (liminf_const _)
  have hne : ∫⁻ ω, (ENNReal.ofReal (Y0 ω))⁻¹ ^ p ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top) hfat
  have hpos0 : ∀ᵐ ω ∂μ, 0 < Y0 ω := by
    filter_upwards [ae_lt_top' hg0 hne] with ω h
    rw [ENNReal.rpow_lt_top_iff_of_pos hp, ENNReal.inv_lt_top, ENNReal.ofReal_pos] at h
    exact h
  have hinv_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => (Y n ω)⁻¹) atTop (𝓝 ((Y0 ω)⁻¹)) := by
    filter_upwards [hlim, hpos0] with ω h h0
    exact h.inv₀ h0.ne'
  have hlower : eLpNorm (fun ω => (Y0 ω)⁻¹) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hmeas n).aemeasurable.inv.aestronglyMeasurable) _ hinv_lim).trans
      ((liminf_le_liminf (Eventually.of_forall hlow)).trans_eq (liminf_const _))
  exact ⟨hpos0, ⟨⟨hY0, hupper.trans_lt ENNReal.ofReal_lt_top⟩, hupper⟩,
    ⟨⟨hY0.aemeasurable.inv.aestronglyMeasurable, hlower.trans_lt ENNReal.ofReal_lt_top⟩, hlower⟩⟩

end
end Paper
