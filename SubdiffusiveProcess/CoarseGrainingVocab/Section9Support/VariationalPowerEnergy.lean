module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalPowerTests
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalLevelEnergy

@[expose] public section

/-!
# Arbitrary-power energy and Sobolev estimates for the Green inverse

Testing by the zero-trace positive power gives its exact energy identity.
The Sobolev readout has coefficient s²/(2s-1), with no qualitative bound
on the solution in that coefficient.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The exact nonlinear Green testing identity. -/
theorem variational_power_energy_identity {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {c rho f : Vec d → ℝ} (hr : CoefficientOn U rho)
    (u w v : H10Function U) (hu : IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f)
    {s : ℝ} (hpair : MoserPowerPair u.toH1Function w.toH1Function v.toH1Function s) :
    (2 * s - 1) * energy c U w.toH1Function =
      s ^ 2 * ∫ x, f x * v.toH1Function.toFun x ∂(weightedMeasure rho).restrict U := by
  rw [integral_weightedMeasure_restrict_eq hU rho _ hr]
  have ht := hu v
  simp only [zero_mul, zero_add, mul_assoc] at ht
  rw [← ht, ← integral_const_mul, energy, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hpair] with x hx
  rw [vecDot_smul_left]
  calc
    _ = c x * ((2 * s - 1) * vecNormSq (w.toH1Function.grad x)) := by
      simp only [vecDot, vecNormSq]
      ring
    _ = c x * (s ^ 2 * vecDot (u.toH1Function.grad x) (v.toH1Function.grad x)) := by rw [hx.1]
    _ = _ := by ring

/-- Sobolev controls the positive-power norm by the corresponding forcing pairing. -/
theorem variational_power_sobolev {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {c rho : Vec d → ℝ}
    (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {p A F : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hSob : SobolevAssumption c rho U p A F)
    (hPoi : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (u : H10Function U)
    (hu : IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f)
    {M : ℝ} (hM : 0 ≤ M)
    (hub : ∀ᵐ x ∂volume.restrict U, |u.toH1Function.toFun x| ≤ M)
    {s : ℝ} (hs : 1 ≤ s) :
    (eLpNorm (fun x => max (u.toH1Function.toFun x) 0 ^ s)
      (ENNReal.ofReal p) ((weightedMeasure rho).restrict U)) ^ 2 ≤
      ENNReal.ofReal (A * (A + 1) * F * ((weightedMeasure rho U).toReal) ^ (-(1 - 2 / p)) *
        (s ^ 2 / (2 * s - 1))) *
        ∫⁻ x, ENNReal.ofReal (|f x| * max (u.toH1Function.toFun x) 0 ^ (2 * s - 1))
          ∂(weightedMeasure rho).restrict U := by
  obtain ⟨w, v, hw, hv, hpair⟩ := exists_variational_power_pair hU u hM hub hs
  have hspos : 0 < 2 * s - 1 := by linarith
  have hc0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x := by
    obtain ⟨_, lo, hi, hlo, hb⟩ := hc
    exact hb.mono fun _ hx => hlo.le.trans hx.1
  have hv0 (x : Vec d) : 0 ≤ v.toH1Function.toFun x := by
    rw [hv]
    exact Real.rpow_nonneg (le_max_right _ _) _
  have hid : energy c U w.toH1Function = s ^ 2 / (2 * s - 1) *
      ∫ x, f x * v.toH1Function.toFun x ∂(weightedMeasure rho).restrict U := by
    have h := variational_power_energy_identity hU.isOpen.measurableSet hr u w v hu hpair
    apply (mul_left_cancel₀ hspos.ne')
    calc
      _ = _ := h
      _ = _ := by
        rw [div_eq_mul_inv]
        calc
          _ = s ^ 2 * ((2 * s - 1) * (2 * s - 1)⁻¹) *
              (∫ x, f x * v.toH1Function.toFun x ∂(weightedMeasure rho).restrict U) := by
            rw [mul_inv_cancel₀ hspos.ne', mul_one]
          _ = _ := by ring
  have hE : ENNReal.ofReal (energy c U w.toH1Function) ≤ ENNReal.ofReal (s ^ 2 / (2 * s - 1)) *
      ∫⁻ x, ENNReal.ofReal (|f x| * v.toH1Function.toFun x) ∂(weightedMeasure rho).restrict U := by
    rw [hid, ENNReal.ofReal_mul (by positivity : 0 ≤ s ^ 2 / (2 * s - 1))]
    refine mul_le_mul' le_rfl ?_
    calc
      _ ≤ ‖∫ x, f x * v.toH1Function.toFun x ∂(weightedMeasure rho).restrict U‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖f x * v.toH1Function.toFun x‖ₑ ∂(weightedMeasure rho).restrict U :=
        enorm_integral_le_lintegral_enorm _
      _ = _ := by
        apply lintegral_congr
        intro x
        rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 x)]
  have hS := sobolev_energy_bound_of_sobolevAssumption_poincareAssumption hA hF hc0 hSob hPoi w
  have h := hS.trans (mul_le_mul' le_rfl hE)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at h
  have hwMeas : AEStronglyMeasurable w.toH1Function.toFun
      ((volume.withDensity (fun x => ENNReal.ofReal (rho x))).restrict U) := by
    simpa only [weightedMeasure] using!
      (memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr
        w.toH1Function.memL2).aestronglyMeasurable
  rw [lpSq, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hwMeas] at h
  simpa only [hw, hv, weightedMeasure] using! h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
