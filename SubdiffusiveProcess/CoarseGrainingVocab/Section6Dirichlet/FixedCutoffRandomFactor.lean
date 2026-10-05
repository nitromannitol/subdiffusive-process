module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffPrebalance

@[expose] public section

/-!
# Fixed-cutoff Dirichlet random factor

The GMC energy carrier is controlled by the same simultaneous response
prefactor.  Consequently the final pointwise random factor is a cubic
polynomial of that one prefactor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The universal deterministic constant produced by the fixed-cutoff
integer balance. -/
def fixedCutoffDirichletBalanceConstant : ℝ :=
  Real.rpow 3 fixedCutoffDirichletS1 +
    Real.rpow 3 fixedCutoffDirichletS2 + 1

/-- The response-only random factor after deterministic substitution. -/
def fixedCutoffDirichletRandomFactor
    {Omega : Type*} (W : Omega → ℝ) (omega : Omega) : ℝ :=
  1 + fixedCutoffDirichletBalanceConstant *
    (1 + W omega) ^ (2 : ℕ) * (2 + 2 * W omega)

theorem fixedCutoffDirichletBalanceConstant_pos :
    0 < fixedCutoffDirichletBalanceConstant := by
  unfold fixedCutoffDirichletBalanceConstant
  have h1 : 0 < Real.rpow 3 fixedCutoffDirichletS1 :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2 : 0 < Real.rpow 3 fixedCutoffDirichletS2 :=
    Real.rpow_pos_of_pos (by norm_num) _
  linarith

theorem one_le_fixedCutoffDirichletRandomFactor
    {Omega : Type*} {W : Omega → ℝ}
    (hW : ∀ omega, 0 ≤ W omega) (omega : Omega) :
    1 ≤ fixedCutoffDirichletRandomFactor W omega := by
  unfold fixedCutoffDirichletRandomFactor
  have hlinear : 0 ≤ 2 + 2 * W omega := by linarith [hW omega]
  have hproduct : 0 ≤ fixedCutoffDirichletBalanceConstant *
      (1 + W omega) ^ (2 : ℕ) * (2 + 2 * W omega) :=
    mul_nonneg
      (mul_nonneg fixedCutoffDirichletBalanceConstant_pos.le (sq_nonneg _))
      hlinear
  linarith

theorem coefficientMeasurable_fixedCutoffDirichletRandomFactor
    {Omega : Type*} {d : ℕ} (A : Omega → Vec d → ℝ) {W : Omega → ℝ}
    (hW : CoefficientMeasurable A W) :
    CoefficientMeasurable A (fixedCutoffDirichletRandomFactor W) := by
  let : MeasurableSpace Omega := coefficientSigma A
  unfold fixedCutoffDirichletRandomFactor
  exact measurable_const.add
    (((measurable_const.mul ((measurable_const.add hW).pow_const 2))).mul
      (measurable_const.add (measurable_const.mul hW)))

/-- A fourth moment of `1 + W` pays the response-only cubic factor. -/
theorem fixedCutoffDirichletRandomFactor_le_fourthPower
    {Omega : Type*} {W : Omega → ℝ}
    (hW : ∀ omega, 0 ≤ W omega) (omega : Omega) :
    fixedCutoffDirichletRandomFactor W omega ≤
      (1 + 2 * fixedCutoffDirichletBalanceConstant) *
        (1 + W omega) ^ (4 : ℕ) := by
  let x := 1 + W omega
  have hx : 1 ≤ x := by dsimp only [x]; linarith [hW omega]
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hC : 0 ≤ fixedCutoffDirichletBalanceConstant :=
    fixedCutoffDirichletBalanceConstant_pos.le
  have hxsub : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hfour : 0 ≤ x ^ (4 : ℕ) - 1 := by
    have hfourBase : 1 ≤ x ^ (4 : ℕ) := by
      simpa only [one_pow] using
      pow_le_pow_left₀ zero_le_one hx 4
    exact sub_nonneg.mpr hfourBase
  have hcubic : 0 ≤ 2 * fixedCutoffDirichletBalanceConstant *
      x ^ (3 : ℕ) * (x - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (pow_nonneg hx0 3)) hxsub
  unfold fixedCutoffDirichletRandomFactor
  rw [show W omega = x - 1 by dsimp only [x]; ring]
  rw [show 1 + (x - 1) = x by ring]
  change 1 + fixedCutoffDirichletBalanceConstant * x ^ (2 : ℕ) *
      (2 + 2 * (x - 1)) ≤
    (1 + 2 * fixedCutoffDirichletBalanceConstant) * x ^ (4 : ℕ)
  nlinarith [hfour, hcubic]

/-- The `4q` response moment used in the manuscript controls the final
response-only random factor in `L^q`. -/
theorem eLpNorm_fixedCutoffDirichletRandomFactor_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {q B : ℝ} {W : Omega → ℝ}
    (hq : 1 ≤ q) (hB : 0 ≤ B) (hW : ∀ omega, 0 ≤ W omega)
    (hWMeas : AEStronglyMeasurable W mu)
    (hWNorm : eLpNorm W (ENNReal.ofReal (4 * q)) mu ≤ ENNReal.ofReal B) :
    eLpNorm (fixedCutoffDirichletRandomFactor W) (ENNReal.ofReal q) mu ≤
      ENNReal.ofReal
        ((1 + 2 * fixedCutoffDirichletBalanceConstant) * (1 + B) ^ (4 : ℕ)) := by
  let F : Omega → ℝ := fun omega ↦ 1 + W omega
  let C : ℝ := 1 + 2 * fixedCutoffDirichletBalanceConstant
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hq4 : 1 ≤ 4 * q := by nlinarith
  have hFnonneg : ∀ omega, 0 ≤ F omega := fun omega ↦ by
    dsimp only [F]
    linarith [hW omega]
  have hFMeas : AEStronglyMeasurable F mu := by
    exact aestronglyMeasurable_const.add hWMeas
  have hOneMeas : AEStronglyMeasurable (fun _ : Omega ↦ (1 : ℝ)) mu :=
    aestronglyMeasurable_const
  have hq4ENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * q) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq4
  have hOneNorm : eLpNorm (fun _ : Omega ↦ (1 : ℝ))
      (ENNReal.ofReal (4 * q)) mu = 1 := by
    rw [eLpNorm_const (1 : ℝ) (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      (IsProbabilityMeasure.ne_zero mu)]
    norm_num
  have hFNorm : eLpNorm F (ENNReal.ofReal (4 * q)) mu ≤
      ENNReal.ofReal (1 + B) := by
    calc
      eLpNorm F (ENNReal.ofReal (4 * q)) mu ≤
          eLpNorm (fun _ : Omega ↦ (1 : ℝ)) (ENNReal.ofReal (4 * q)) mu +
            eLpNorm W (ENNReal.ofReal (4 * q)) mu := by
        simpa only [F, Pi.add_apply] using!
          eLpNorm_add_le (f := fun _ : Omega => (1 : ℝ)) (g := W) (μ := mu) hq4ENN
      _ ≤ 1 + ENNReal.ofReal B := by rw [hOneNorm]; gcongr
      _ = ENNReal.ofReal (1 + B) := by
        rw [← ENNReal.ofReal_one, ENNReal.ofReal_add zero_le_one hB]
  have hPowerNorm :
      eLpNorm (fun omega ↦ F omega ^ (4 : ℕ)) (ENNReal.ofReal q) mu =
        eLpNorm F (ENNReal.ofReal (4 * q)) mu ^ (4 : ℕ) := by
    have hpow := eLpNorm_norm_rpow (p := ENNReal.ofReal q) (μ := mu) F hFMeas
      (q := (4 : ℝ)) (by norm_num)
    have hfun : (fun omega ↦ ‖F omega‖ ^ (4 : ℝ)) =
        fun omega ↦ F omega ^ (4 : ℕ) := by
      funext omega
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg omega)]
      exact Real.rpow_natCast (F omega) 4
    rw [hfun] at hpow
    have hexponent : ENNReal.ofReal q * ENNReal.ofReal (4 : ℝ) =
        ENNReal.ofReal (4 * q) := by
      rw [← ENNReal.ofReal_mul hq0.le]
      congr 1
      ring
    rw [hexponent] at hpow
    calc
      eLpNorm (fun omega ↦ F omega ^ (4 : ℕ)) (ENNReal.ofReal q) mu =
          eLpNorm F (ENNReal.ofReal (4 * q)) mu ^ (4 : ℝ) := hpow
      _ = eLpNorm F (ENNReal.ofReal (4 * q)) mu ^ (4 : ℕ) :=
        ENNReal.rpow_natCast _ 4
  have hPowerBound : eLpNorm (fun omega ↦ F omega ^ (4 : ℕ))
      (ENNReal.ofReal q) mu ≤ ENNReal.ofReal (1 + B) ^ (4 : ℕ) := by
    rw [hPowerNorm]
    exact pow_le_pow_left₀ (by positivity) hFNorm 4
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith [fixedCutoffDirichletBalanceConstant_pos]
  have hpoint : ∀ omega, ‖fixedCutoffDirichletRandomFactor W omega‖ ≤
      C * F omega ^ (4 : ℕ) := by
    intro omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (zero_le_one.trans (one_le_fixedCutoffDirichletRandomFactor hW omega))]
    exact fixedCutoffDirichletRandomFactor_le_fourthPower hW omega
  have hmono : eLpNorm (fixedCutoffDirichletRandomFactor W)
      (ENNReal.ofReal q) mu ≤
      eLpNorm (fun omega ↦ C * F omega ^ (4 : ℕ))
        (ENNReal.ofReal q) mu :=
    eLpNorm_mono_ae_real
      (by unfold fixedCutoffDirichletRandomFactor; fun_prop)
      (Filter.Eventually.of_forall hpoint)
  calc
    eLpNorm (fixedCutoffDirichletRandomFactor W) (ENNReal.ofReal q) mu ≤
        eLpNorm (fun omega ↦ C * F omega ^ (4 : ℕ))
          (ENNReal.ofReal q) mu := hmono
    _ = ENNReal.ofReal C *
        eLpNorm (fun omega ↦ F omega ^ (4 : ℕ))
          (ENNReal.ofReal q) mu := by
      change eLpNorm (C • fun omega ↦ F omega ^ (4 : ℕ))
          (ENNReal.ofReal q) mu = _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (1 + B) ^ (4 : ℕ) := by
      gcongr
    _ = ENNReal.ofReal
        ((1 + 2 * fixedCutoffDirichletBalanceConstant) *
          (1 + B) ^ (4 : ℕ)) := by
      dsimp only [C]
      rw [← ENNReal.ofReal_pow (by linarith : 0 ≤ 1 + B),
        ← ENNReal.ofReal_mul hC]

/-- Pointwise response-envelope substitution with the final random factor. -/
theorem dirichletPrebalanceCore_le_fixedCutoffDirichletRandomFactor_mul
    {Omega : Type*} {theta : ℝ} {W : Omega → ℝ}
    {E1 E2 : Omega → ℝ} (N : ℕ) (omega : Omega)
    (htheta : 0 ≤ theta) (hW : 0 ≤ W omega) (hE2 : 0 ≤ E2 omega)
    (hResponseOne : E1 omega ≤
      W omega * fixedCutoffDirichletResponseWeight theta N)
    (hResponseTwo : E2 omega ≤
      W omega * fixedCutoffDirichletResponseWeight theta N) :
    dirichletPrebalanceCore fixedCutoffDirichletS1 fixedCutoffDirichletS2
        (fixedCutoffDirichletBalanceScale theta N)
        (E1 omega) (E2 omega) (1 + 2 * E2 omega) ≤
      fixedCutoffDirichletRandomFactor W omega *
        fixedCutoffDirichletTargetWeight theta N := by
  have hcore := fixedCutoffDirichlet_prebalanceCore_le_of_response N
    htheta hW hE2 hResponseOne hResponseTwo
  have hT : 0 ≤ fixedCutoffDirichletTargetWeight theta N :=
    Real.rpow_nonneg (by norm_num) _
  calc
    _ ≤ fixedCutoffDirichletBalanceConstant *
        (1 + W omega) ^ (2 : ℕ) * (2 + 2 * W omega) *
        fixedCutoffDirichletTargetWeight theta N := by
      exact hcore
    _ ≤ fixedCutoffDirichletRandomFactor W omega *
        fixedCutoffDirichletTargetWeight theta N := by
      apply mul_le_mul_of_nonneg_right _ hT
      unfold fixedCutoffDirichletRandomFactor
      linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
