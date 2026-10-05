module

public import SubdiffusiveProcess.CoarseGrainingVocab.ReciprocalLowerSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepStationaryForcing

@[expose] public section




open MeasureTheory ProbabilityTheory Homogenization
open Homogenization.IndependentSums

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private abbrev Field (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialField d

/-- The raw second exponential moment of one zero-scale shell at the origin. -/
def oneShellExpTwoMoment {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : ℝ :=
  ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (2 * g 0)
    ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure

/-- The raw second exponential moment is Bochner integrable. -/
theorem integrable_exp_two_zeroPotential_at_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.exp (2 * g 0))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let A : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta
  have hbase : 0 < 1 + Real.log 2 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hA : 0 < A :=
    mul_pos (Real.rpow_pos_of_pos hbase _) M.shellPrefix.delta_pos
  have hX := isBigO_gammaTwo_potentialCoordinate_apply M 0 0
  have hXm : AEMeasurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega 0 0) M.P.toMeasure :=
    ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0)).aemeasurable
  have hIntSample : Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => Real.exp (2 * omega 0 0))
      M.P.toMeasure := by
    exact integrable_exp_mul_of_isBigO_gammaSigma_of_one_lt
      (μ := M.P.toMeasure) hXm (by norm_num : (1 : ℝ) < 2) hA
        (by norm_num) (by simpa [A] using hX)
  let evalSample : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => omega 0 0
  let evalField : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => g 0
  let phi : ℝ → ℝ := fun z => Real.exp (2 * z)
  have hevalSample : Measurable evalSample :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0)
  have hevalField : Measurable evalField :=
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0
  have hphi : Measurable phi := (measurable_const.mul measurable_id).exp
  have hmap := map_potentialCoordinate_apply_eq_zero M 0 0
  have hField : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.exp (2 * g 0))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    have hMapSample : Integrable phi (Measure.map evalSample M.P.toMeasure) :=
      (integrable_map_measure hphi.aestronglyMeasurable
        hevalSample.aemeasurable).2 (by simpa [phi, evalSample, Function.comp_def] using! hIntSample)
    rw [hmap] at hMapSample
    exact (integrable_map_measure hphi.aestronglyMeasurable
      hevalField.aemeasurable).1 hMapSample
  exact hField

theorem oneShellExpTwoMoment_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < oneShellExpTwoMoment M := by
  unfold oneShellExpTwoMoment
  exact integral_exp_pos (integrable_exp_two_zeroPotential_at_zero M)

/-- One centered shell contributes `exp(-2 tauSq) * E[exp(2 g₀(0))]` to
the second moment of the multiplicative block. -/
def oneShellCenteredExpTwoMoment {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : ℝ :=
  Real.exp (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P) * oneShellExpTwoMoment M

theorem oneShellCenteredExpTwoMoment_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < oneShellCenteredExpTwoMoment M := by
  exact mul_pos (Real.exp_pos _) (oneShellExpTwoMoment_pos M)

/-- The one-shell cumulant increment `psi(2) - 2 psi(1)`. -/
def oneStepCumulant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : ℝ :=
  Real.log (oneShellExpTwoMoment M) -
    2 * _root_.SubdiffusiveProcess.Model.tauSq M.P

theorem oneShellCenteredExpTwoMoment_eq_exp_oneStepCumulant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    oneShellCenteredExpTwoMoment M = Real.exp (oneStepCumulant M) := by
  rw [oneShellCenteredExpTwoMoment, oneStepCumulant, Real.exp_sub,
    Real.exp_log (oneShellExpTwoMoment_pos M)]
  rw [show -2 * _root_.SubdiffusiveProcess.Model.tauSq M.P =
    -(2 * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring, Real.exp_neg]
  ring

private theorem integral_exp_two_centered_potentialCoordinate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (x : Vec d) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        Real.exp (2 * (omega k x - _root_.SubdiffusiveProcess.Model.tauSq M.P))
        ∂M.P.toMeasure = oneShellCenteredExpTwoMoment M := by
  let evalK : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => omega k x
  let eval0 : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => g 0
  let phi : ℝ → ℝ := fun z => Real.exp (2 * z)
  have hevalK : Measurable evalK :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)
  have heval0 : Measurable eval0 :=
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0
  have hphi : Measurable phi := (measurable_const.mul measurable_id).exp
  have hmap := map_potentialCoordinate_apply_eq_zero M k x
  have hraw : ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, Real.exp (2 * omega k x) ∂M.P.toMeasure =
      oneShellExpTwoMoment M := by
    calc
      ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, Real.exp (2 * omega k x) ∂M.P.toMeasure =
          ∫ z, phi z ∂Measure.map evalK M.P.toMeasure := by
        exact (integral_map hevalK.aemeasurable hphi.aestronglyMeasurable).symm
      _ = ∫ z, phi z ∂Measure.map eval0
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by rw [hmap]
      _ = ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (2 * g 0)
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
        exact integral_map heval0.aemeasurable hphi.aestronglyMeasurable
      _ = oneShellExpTwoMoment M := rfl
  calc
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        Real.exp (2 * (omega k x - _root_.SubdiffusiveProcess.Model.tauSq M.P))
        ∂M.P.toMeasure =
      Real.exp (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, Real.exp (2 * omega k x) ∂M.P.toMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with omega
      rw [← Real.exp_add]
      congr 1
      ring
    _ = oneShellCenteredExpTwoMoment M := by
      rw [hraw]
      rfl

private theorem integrable_exp_two_centered_potentialCoordinate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (x : Vec d) :
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      Real.exp (2 * (omega k x - _root_.SubdiffusiveProcess.Model.tauSq M.P)))
      M.P.toMeasure := by
  let A : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta
  have hbase : 0 < 1 + Real.log 2 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hA : 0 < A :=
    mul_pos (Real.rpow_pos_of_pos hbase _) M.shellPrefix.delta_pos
  have hXm : AEMeasurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k x) M.P.toMeasure :=
    ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)).aemeasurable
  have hraw : Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => Real.exp (2 * omega k x))
      M.P.toMeasure := by
    exact integrable_exp_mul_of_isBigO_gammaSigma_of_one_lt
      (μ := M.P.toMeasure) hXm (by norm_num : (1 : ℝ) < 2) hA
        (by norm_num) (by
          simpa [A] using isBigO_gammaTwo_potentialCoordinate_apply M k x)
  have h := hraw.const_mul
    (Real.exp (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P))
  convert h using 1
  funext omega
  rw [← Real.exp_add]
  congr 1
  ring

/-- Exact second moment of the multiplicative suffix ratio. -/
theorem integral_oneStepRatio_sq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (oneStepOriginMultiplier M n h omega + 1) ^ 2
        ∂M.P.toMeasure = (oneShellCenteredExpTwoMoment M) ^ h := by
  let X : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun k omega =>
    2 * (omega k 0 - _root_.SubdiffusiveProcess.Model.tauSq M.P)
  let s : Finset ℕ := cutoffShellIndices (n + h) (n : ℤ)
  have hIndep : iIndepFun X M.P.toMeasure := by
    simpa [X, Function.comp_def] using M.shellPrefix.independent.comp
      (fun _ g => 2 * (g 0 - _root_.SubdiffusiveProcess.Model.tauSq M.P))
      (fun _ => measurable_const.mul
        ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).sub
          measurable_const))
  have hMeas : ∀ k, Measurable (X k) := fun k =>
    measurable_const.mul
      (((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).comp
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)).sub
          measurable_const)
  have hTerm : ∀ k ∈ s,
      Integrable (fun omega => Real.exp (1 * X k omega)) M.P.toMeasure := by
    intro k _
    simpa [X] using integrable_exp_two_centered_potentialCoordinate M k 0
  have hsum := hIndep.integrable_exp_mul_sum (t := (1 : ℝ)) hMeas hTerm
  have hFactor : ∀ k, ProbabilityTheory.mgf (X k) M.P.toMeasure 1 =
      oneShellCenteredExpTwoMoment M := by
    intro k
    rw [ProbabilityTheory.mgf]
    simpa [X] using integral_exp_two_centered_potentialCoordinate M k 0
  have hcard : s.card = h := by
    dsimp [s]
    rw [cutoffShellIndices_card (n + h) (n : ℤ) (by omega) (by omega)]
    omega
  calc
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (oneStepOriginMultiplier M n h omega + 1) ^ 2
        ∂M.P.toMeasure =
      ProbabilityTheory.mgf (∑ k ∈ s, X k) M.P.toMeasure 1 := by
      apply integral_congr_ae
      filter_upwards with omega
      unfold oneStepOriginMultiplier
      rw [cutoffRatioMinusOne_eq_exp_shell M (n + h) (n : ℤ) omega 0
        (by omega) (by omega)]
      simp only [sub_add_cancel]
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [Finset.sum_apply, one_mul]
      dsimp [s, X, cutoffShellSum]
      rw [mul_sub, Finset.mul_sum]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hcard]
      push_cast
      ring
    _ = ∏ k ∈ s, ProbabilityTheory.mgf (X k) M.P.toMeasure 1 :=
      hIndep.mgf_sum hMeas s
    _ = ∏ _k ∈ s, oneShellCenteredExpTwoMoment M := by
      apply Finset.prod_congr rfl
      intro k _
      exact hFactor k
    _ = (oneShellCenteredExpTwoMoment M) ^ h := by
      rw [Finset.prod_const, hcard]

/-- The suffix multiplier is centered. -/
theorem integral_oneStepOriginMultiplier_eq_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, oneStepOriginMultiplier M n h omega
        ∂M.P.toMeasure = 0 := by
  have hX : Integrable (oneStepOriginMultiplier M n h) M.P.toMeasure :=
    (memLp_two_oneStepOriginMultiplier M n h hh).integrable one_le_two
  have hconst : Integrable (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => (1 : ℝ)) M.P.toMeasure :=
    integrable_const 1
  have hmean := integral_cutoffRatio M (n + h) (n : ℤ) 0 (by omega) (by omega)
  change (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, oneStepOriginMultiplier M n h omega + 1
    ∂M.P.toMeasure) = 1 at hmean
  rw [integral_add hX hconst, integral_const] at hmean
  have hprob : M.P.toMeasure.real Set.univ = 1 := probReal_univ
  rw [hprob, one_smul] at hmean
  linarith

/-- Exact scalar energy of the centered multiplicative suffix. -/
theorem integral_oneStepOriginMultiplier_sq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (oneStepOriginMultiplier M n h omega) ^ 2
        ∂M.P.toMeasure = (oneShellCenteredExpTwoMoment M) ^ h - 1 := by
  have hX2 := (memLp_two_oneStepOriginMultiplier M n h hh).integrable_sq
  have hX := (memLp_two_oneStepOriginMultiplier M n h hh).integrable one_le_two
  have htwoX : Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      2 * oneStepOriginMultiplier M n h omega) M.P.toMeasure := hX.const_mul 2
  have hone : Integrable (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => (1 : ℝ)) M.P.toMeasure :=
    integrable_const 1
  have hsumInt : Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (oneStepOriginMultiplier M n h omega) ^ 2 +
        2 * oneStepOriginMultiplier M n h omega) M.P.toMeasure := by
    exact hX2.add htwoX
  have houter :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        ((oneStepOriginMultiplier M n h omega) ^ 2 +
          2 * oneStepOriginMultiplier M n h omega) + 1 ∂M.P.toMeasure) =
        (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          ((oneStepOriginMultiplier M n h omega) ^ 2 +
            2 * oneStepOriginMultiplier M n h omega) ∂M.P.toMeasure) +
          ∫ _omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, 1 ∂M.P.toMeasure := by
    exact integral_add hsumInt hone
  have hinner :
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        ((oneStepOriginMultiplier M n h omega) ^ 2 +
          2 * oneStepOriginMultiplier M n h omega) ∂M.P.toMeasure) =
        (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (oneStepOriginMultiplier M n h omega) ^ 2
          ∂M.P.toMeasure) +
          ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, 2 * oneStepOriginMultiplier M n h omega
            ∂M.P.toMeasure := by
    exact integral_add hX2 htwoX
  have hexpand : ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      (oneStepOriginMultiplier M n h omega + 1) ^ 2 ∂M.P.toMeasure =
      (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (oneStepOriginMultiplier M n h omega) ^ 2
          ∂M.P.toMeasure) +
        2 * (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, oneStepOriginMultiplier M n h omega
          ∂M.P.toMeasure) + 1 := by
    rw [show (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        (oneStepOriginMultiplier M n h omega + 1) ^ 2) =
        fun omega => (oneStepOriginMultiplier M n h omega) ^ 2 +
          2 * oneStepOriginMultiplier M n h omega + 1 by
      funext omega
      ring]
    rw [houter, hinner, integral_const_mul, integral_const, probReal_univ]
    simp
  rw [integral_oneStepRatio_sq M n h hh,
    integral_oneStepOriginMultiplier_eq_zero M n h hh] at hexpand
  linarith

/-- Cumulant form of the exact suffix-energy identity. -/
theorem integral_oneStepOriginMultiplier_sq_eq_exp_cumulant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (oneStepOriginMultiplier M n h omega) ^ 2
        ∂M.P.toMeasure = Real.exp ((h : ℝ) * oneStepCumulant M) - 1 := by
  rw [integral_oneStepOriginMultiplier_sq M n h hh,
    oneShellCenteredExpTwoMoment_eq_exp_oneStepCumulant]
  rw [← Real.exp_nat_mul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
