import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.InteriorVariationalGreen
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserVariationalGreen

/-!
# The first quantitative gain of the variational Green inverse

Testing with the solution, weighted Cauchy--Schwarz, and the supplied
Poincare inequality give the `L²` operator bound `A F`. Combining it with
the supplied Sobolev inequality gives the squared `L² → Lᵖ` gain with
coefficient `A² (A+1) F² M^{-(1-2/p)}`. The qualitative ellipticity and
density bounds used for existence do not occur in either estimate.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Energy and `L²` bounds for any zero-trace variational Green solution. -/
theorem interior_green_energy_l2_bound {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {c rho : Vec d → ℝ}
    (hr : CoefficientOn U rho)
    {A F : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hPoi : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    (g : H10Function U) (hg : IsMassiveWeakSolutionOn c rho 0 U g.toH1Function f) :
    ENNReal.ofReal (energy c U g.toH1Function) ≤ ENNReal.ofReal (A * F) * lpSq rho U 2 f ∧
    eLpNorm g.toH1Function.toFun 2 ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal (A * F) * eLpNorm f 2 ((weightedMeasure rho).restrict U) := by
  let mu := (weightedMeasure rho).restrict U
  have hgmem : MemLp g.toH1Function.toFun 2 mu :=
    memLp_weighted_of_volume_restrict hU hr g.toH1Function.memL2
  have hid : energy c U g.toH1Function = ∫ x, f x * g.toH1Function.toFun x ∂mu := by
    rw [integral_weightedMeasure_restrict_eq hU rho _ hr]
    have ht := hg g
    simpa only [energy, zero_mul, zero_add, vecDot_smul_left, mul_assoc] using ht
  have hpair : ENNReal.ofReal (energy c U g.toH1Function) ≤
      eLpNorm f 2 mu * eLpNorm g.toH1Function.toFun 2 mu := by
    calc
      ENNReal.ofReal (energy c U g.toH1Function) ≤
          ‖∫ x, f x * g.toH1Function.toFun x ∂mu‖ₑ := by
        rw [hid, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖f x * g.toH1Function.toFun x‖ₑ ∂mu :=
        enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => f x * g.toH1Function.toFun x) 1 mu :=
        eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm f 2 mu * eLpNorm g.toH1Function.toFun 2 mu := by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
            hgmem.aestronglyMeasurable hf.aestronglyMeasurable)
  have hPoi' := hPoi g
  rw [ENNReal.ofReal_mul (mul_nonneg hA hF)] at hPoi'
  simp only [lpSq, ENNReal.ofReal_ofNat] at hPoi'
  change eLpNorm g.toH1Function.toFun 2 mu ^ 2 ≤
    ENNReal.ofReal (A * F) * ENNReal.ofReal (energy c U g.toH1Function) at hPoi'
  have hl2 : eLpNorm g.toH1Function.toFun 2 mu ≤ ENNReal.ofReal (A * F) * eLpNorm f 2 mu := by
    by_cases hz : eLpNorm g.toH1Function.toFun 2 mu = 0
    · rw [hz]
      exact zero_le _
    · apply (ENNReal.mul_le_mul_iff_left hz hgmem.eLpNorm_ne_top).mp
      simpa only [pow_two, mul_assoc] using hPoi'.trans (mul_le_mul' le_rfl hpair)
  refine ⟨?_, hl2⟩
  calc
    ENNReal.ofReal (energy c U g.toH1Function) ≤
        eLpNorm f 2 mu * (ENNReal.ofReal (A * F) * eLpNorm f 2 mu) :=
      hpair.trans (mul_le_mul' le_rfl hl2)
    _ = ENNReal.ofReal (A * F) * lpSq rho U 2 f := by
      simp only [lpSq, weightedMeasure, ENNReal.ofReal_ofNat, mu]
      ring

/-- The first Green smoothing rung, with exactly the mass exponent dictated
by the frozen Sobolev assumption. -/
theorem interior_green_lpSq_gain {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {c rho : Vec d → ℝ}
    (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {p A F : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hSob : SobolevAssumption c rho U p A F)
    (hPoi : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    (g : H10Function U) (hg : IsMassiveWeakSolutionOn c rho 0 U g.toH1Function f) :
    lpSq rho U p g.toH1Function.toFun ≤
      ENNReal.ofReal (A ^ 2 * (A + 1) * F ^ 2 *
        ((weightedMeasure rho U).toReal) ^ (-(1 - 2 / p))) * lpSq rho U 2 f := by
  obtain ⟨lo, hi, hlo, hcb⟩ := hc.2
  have hc0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x :=
    hcb.mono fun _ hx => hlo.le.trans hx.1
  have hform := sobolev_energy_bound_of_sobolevAssumption_poincareAssumption
    hA hF hc0 hSob hPoi g
  have henergy := (interior_green_energy_l2_bound hU hr hA hF hPoi hf g hg).1
  refine hform.trans ((mul_le_mul' le_rfl henergy).trans_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
