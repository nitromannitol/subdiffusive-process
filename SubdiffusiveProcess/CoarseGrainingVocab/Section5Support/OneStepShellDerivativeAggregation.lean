module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellDerivativeEnvelope

@[expose] public section

/-!
# Lognormal/moment aggregation for the one-step derivative

This file performs the manuscript's Hölder step after the `(g2)` derivative
estimate.  The two eighth moments are kept as named source-scale constants;
their product is the fourth-moment bound for the literal differentiated
suffix multiplier.
-/

open MeasureTheory Homogenization Homogenization.IndependentSums
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- The landed cutoff-moment bound at exponent eight for a block of length
`h`. -/
def oneStepRatioMinusOneEightBound {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ) : ℝ :=
  cutoffMomentConst * Real.sqrt 8 * M.delta * Real.sqrt (h : ℝ) *
    Real.exp (cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ))

/-- The uniform eighth-moment bound for the dimensionless derivative gauge. -/
def oneStepDerivativeGaugeEightBound {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : ℝ :=
  gammaMomentConst 2 * Real.sqrt 8 *
    (gammaTriangleConst 2 *
      ((1 / 2) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)))

theorem oneStepRatioMinusOneEightBound_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ) :
    0 ≤ oneStepRatioMinusOneEightBound M h := by
  unfold oneStepRatioMinusOneEightBound
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg _))
        M.shellPrefix.delta_pos.le)
      (Real.sqrt_nonneg _))
    (Real.exp_pos _).le

theorem oneStepDerivativeGaugeEightBound_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    0 ≤ oneStepDerivativeGaugeEightBound M := by
  unfold oneStepDerivativeGaugeEightBound
  exact mul_nonneg
    (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _))
    (mul_nonneg (gammaTriangleConst_pos (σ := 2)).le
      (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith) _) M.shellPrefix.delta_pos.le)))

/-- `L^8(Ω)` norm of the centered suffix ratio minus one. -/
theorem eLpNorm_oneStepRatioMinusOne_eight_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (x : Vec d)
    (hh : 0 < h) :
    eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1)
      8 M.P.toMeasure ≤ ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) := by
  have hn : (-1 : ℤ) ≤ (n : ℤ) := by omega
  have hnm : (n : ℤ) < ((n + h : ℕ) : ℤ) := by
    exact_mod_cast Nat.lt_add_of_pos_right hh
  have hraw := integral_abs_cutoffRatioMinusOne_rpow_root_le_raw
    M (n + h) (n : ℤ) x 8 (by norm_num) hn hnm
  let R : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega =>
    Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
      (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1
  have hReq : R = fun omega => cutoffRatioMinusOne M (n + h) (n : ℤ) omega x := by
    funext omega
    dsimp [R]
    rw [cutoffRatioMinusOne_eq_exp_shell M (n + h) (n : ℤ) omega x hn hnm]
    have hdiff : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
      push_cast
      ring
    rw [hdiff]
  have hRmeas : Measurable R := by
    exact (Real.measurable_exp.comp
      ((measurable_cutoffShellSum (n + h) (n : ℤ) x).sub_const _)).sub_const _
  have hRint : Integrable (fun omega => |R omega| ^ (8 : ℝ)) M.P.toMeasure := by
    rw [hReq]
    exact hraw.1
  have hRmem : MemLp R 8 M.P.toMeasure := by
    apply (integrable_norm_rpow_iff hRmeas.aestronglyMeasurable
      (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num : (8 : ℝ≥0∞) ≠ ∞)).1
    simpa [Real.norm_eq_abs] using hRint
  have hroot :
      (∫ omega, |R omega| ^ (8 : ℝ) ∂M.P.toMeasure) ^ (8 : ℝ)⁻¹ ≤
        oneStepRatioMinusOneEightBound M h := by
    rw [hReq]
    have hdiff : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
      push_cast
      ring
    simpa only [oneStepRatioMinusOneEightBound, hdiff] using
      (integral_abs_cutoffRatioMinusOne_rpow_root_le
        M (n + h) (n : ℤ) x 8 (by norm_num) hn hnm)
  rw [show (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
        (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1) = R by rfl]
  rw [hRmem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num : (8 : ℝ≥0∞) ≠ ∞)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal hroot

/-- The positive lognormal suffix multiplier has `L^8` norm at most one plus
the centered cutoff-moment bound. -/
theorem eLpNorm_oneStepRatio_eight_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (x : Vec d)
    (hh : 0 < h) :
    eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
      8 M.P.toMeasure ≤
        ENNReal.ofReal (oneStepRatioMinusOneEightBound M h + 1) := by
  let R : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega =>
    Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
      (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1
  have htri := eLpNorm_add_le (μ := M.P.toMeasure) (f := R) (g := fun _ => (1 : ℝ))
    (by norm_num : (1 : ℝ≥0∞) ≤ 8)
  calc
    eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) 8 M.P.toMeasure =
      eLpNorm (R + fun _ => (1 : ℝ)) 8 M.P.toMeasure := by
        congr 1
        funext omega
        dsimp [R]
        ring
    _ ≤ eLpNorm R 8 M.P.toMeasure +
        eLpNorm (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => (1 : ℝ)) 8 M.P.toMeasure := htri
    _ ≤ ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) + 1 := by
      gcongr
      · simpa only [R] using eLpNorm_oneStepRatioMinusOne_eight_le M n h x hh
      · rw [eLpNorm_const (1 : ℝ) (by norm_num) (NeZero.ne M.P.toMeasure)]
        norm_num
    _ = ENNReal.ofReal (oneStepRatioMinusOneEightBound M h + 1) := by
      rw [ENNReal.ofReal_add (oneStepRatioMinusOneEightBound_nonneg M h) (by norm_num)]
      norm_num

/-- `L^8(Ω)` norm of the geometric derivative gauge. -/
theorem eLpNorm_oneStepDerivativeGauge_eight_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (z : Vec d)
    (hh : 0 < h) :
    eLpNorm (oneStepShellDerivativeGauge n h z) 8 M.P.toMeasure ≤
      ENNReal.ofReal (oneStepDerivativeGaugeEightBound M) := by
  have hmem := memLp_eight_oneStepShellDerivativeGauge M n h z hh
  rw [hmem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num : (8 : ℝ≥0∞) ≠ ∞)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal
    (integral_oneStepShellDerivativeGauge_eighth_root_le M n h z hh)

/-- The fixed-point fourth moment of the differentiated multiplier is the
Hölder product of the lognormal and geometric eighth-moment bounds. -/
theorem eLpNorm_oneStepMultiplierDerivative_majorant_four_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (z x : Vec d)
    (hh : 0 < h) :
    eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          oneStepShellDerivativeGauge n h z omega)
      4 M.P.toMeasure ≤
        ENNReal.ofReal ((oneStepRatioMinusOneEightBound M h + 1) *
          oneStepDerivativeGaugeEightBound M) := by
  let f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega =>
    Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
      (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  let g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := oneStepShellDerivativeGauge n h z
  have hf : AEStronglyMeasurable f M.P.toMeasure :=
    (Real.measurable_exp.comp
      ((measurable_cutoffShellSum (n + h) (n : ℤ) x).sub_const _)).aestronglyMeasurable
  have hg : AEStronglyMeasurable g M.P.toMeasure :=
    (measurable_oneStepShellDerivativeGauge n h z).aestronglyMeasurable
  letI : ENNReal.HolderTriple (8 : ℝ≥0∞) (8 : ℝ≥0∞) (4 : ℝ≥0∞) :=
    { inv_add_inv_eq_inv := by
        rw [← two_mul]
        have h8 : (8 : ℝ≥0∞) = 2 * 4 := by norm_num
        rw [h8, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul] }
  have hholder : eLpNorm (fun omega => f omega * g omega) 4 M.P.toMeasure ≤
      eLpNorm f 8 M.P.toMeasure * eLpNorm g 8 M.P.toMeasure := by
    simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (fun a b : ℝ => a * b) 1 (continuous_fst.mul continuous_snd) hf hg (Filter.Eventually.of_forall fun omega => by simp))
  calc
    eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          oneStepShellDerivativeGauge n h z omega) 4 M.P.toMeasure ≤
      eLpNorm f 8 M.P.toMeasure * eLpNorm g 8 M.P.toMeasure := hholder
    _ ≤ ENNReal.ofReal (oneStepRatioMinusOneEightBound M h + 1) *
        ENNReal.ofReal (oneStepDerivativeGaugeEightBound M) := by
      exact mul_le_mul
        (by simpa only [f] using eLpNorm_oneStepRatio_eight_le M n h x hh)
        (by simpa only [g] using eLpNorm_oneStepDerivativeGauge_eight_le M n h z hh)
        zero_le zero_le
    _ = ENNReal.ofReal ((oneStepRatioMinusOneEightBound M h + 1) *
        oneStepDerivativeGaugeEightBound M) := by
      rw [ENNReal.ofReal_mul (by
        linarith [oneStepRatioMinusOneEightBound_nonneg M h] :
          0 ≤ oneStepRatioMinusOneEightBound M h + 1)]

/-- Dimension-free constant absorbing the lognormal eighth moment on the
one-step range `h ≤ delta⁻¹`. -/
def oneStepRatioEightUniformConst : ℝ :=
  cutoffMomentConst * Real.sqrt 8 * Real.exp (4 * cutoffMomentConst)

theorem oneStepRatioEightUniformConst_pos : 0 < oneStepRatioEightUniformConst := by
  unfold oneStepRatioEightUniformConst
  exact mul_pos (mul_pos cutoffMomentConst_pos (Real.sqrt_pos.mpr (by norm_num)))
    (Real.exp_pos _)

/-- Dimension-only coefficient in the derivative-gauge moment. -/
def oneStepDerivativeGaugeConst : ℝ :=
  gammaMomentConst 2 * Real.sqrt 8 * gammaTriangleConst 2 *
    (1 / 2) * (1 + Real.log 2) ^ (2 : ℝ)⁻¹

theorem oneStepDerivativeGaugeConst_pos : 0 < oneStepDerivativeGaugeConst := by
  unfold oneStepDerivativeGaugeConst
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_pos (mul_pos (mul_pos
    (mul_pos (gammaMomentConst_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num)))
      (gammaTriangleConst_pos (σ := 2))) (by norm_num))
    (Real.rpow_pos_of_pos hlog _)

/-- Final fourth-moment constant for the differentiated suffix multiplier. -/
def oneStepMultiplierDerivativeFourthConst : ℝ :=
  (oneStepRatioEightUniformConst + 1) * oneStepDerivativeGaugeConst

theorem oneStepMultiplierDerivativeFourthConst_pos :
    0 < oneStepMultiplierDerivativeFourthConst := by
  unfold oneStepMultiplierDerivativeFourthConst
  exact mul_pos (by linarith [oneStepRatioEightUniformConst_pos])
    oneStepDerivativeGaugeConst_pos

theorem oneStepDerivativeGaugeEightBound_eq_const_mul {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    oneStepDerivativeGaugeEightBound M = oneStepDerivativeGaugeConst * M.delta := by
  unfold oneStepDerivativeGaugeEightBound oneStepDerivativeGaugeConst
  ring

theorem oneStepRatioMinusOneEightBound_le_uniform {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    oneStepRatioMinusOneEightBound M h ≤ oneStepRatioEightUniformConst := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaHalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  have hdh : M.delta * (h : ℝ) ≤ 1 := by
    have hs : (h : ℝ) ≤ 1 / M.delta := by simpa [one_div] using hscale
    simpa [mul_comm] using (le_div_iff₀ hdelta).mp hs
  have hdeltaSqH : M.delta ^ 2 * (h : ℝ) ≤ M.delta := by
    nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt (h : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (h : ℝ)) ^ 2 = (h : ℝ) := by
    rw [Real.sq_sqrt hh0]
  have hfactor : M.delta * Real.sqrt (h : ℝ) ≤ 1 := by
    have hsq : (M.delta * Real.sqrt (h : ℝ)) ^ 2 ≤ 1 ^ 2 := by
      rw [mul_pow, hsqrtSq]
      nlinarith
    nlinarith [mul_nonneg hdelta.le hsqrt0]
  have hexponent :
      cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ) ≤
        4 * cutoffMomentConst := by
    have hC := cutoffMomentConst_pos.le
    nlinarith
  unfold oneStepRatioMinusOneEightBound oneStepRatioEightUniformConst
  calc
    cutoffMomentConst * Real.sqrt 8 * M.delta * Real.sqrt (h : ℝ) *
        Real.exp (cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ)) =
      (cutoffMomentConst * Real.sqrt 8) *
        (M.delta * Real.sqrt (h : ℝ)) *
        Real.exp (cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ)) := by ring
    _ ≤
      cutoffMomentConst * Real.sqrt 8 * 1 *
        Real.exp (cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg 8)))
        (Real.exp_pos _).le
    _ ≤ cutoffMomentConst * Real.sqrt 8 * 1 *
        Real.exp (4 * cutoffMomentConst) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        (mul_nonneg (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg 8))
          (by norm_num))
    _ = cutoffMomentConst * Real.sqrt 8 * Real.exp (4 * cutoffMomentConst) := by ring

/-- The lognormal eighth-moment estimate with its central-limit prefactor
retained.  This is the sharp `delta * sqrt h` scale used by the nonlinear
weighted-energy comparison. -/
theorem oneStepRatioMinusOneEightBound_le_sqrtScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    oneStepRatioMinusOneEightBound M h ≤
      oneStepRatioEightUniformConst * M.delta * Real.sqrt (h : ℝ) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaSqH : M.delta ^ 2 * (h : ℝ) ≤ M.delta := by
    have hs : (h : ℝ) ≤ 1 / M.delta := by simpa [one_div] using hscale
    have hdh : M.delta * (h : ℝ) ≤ 1 := by
      simpa [mul_comm] using (le_div_iff₀ hdelta).mp hs
    nlinarith
  have hexponent :
      cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ) ≤
        4 * cutoffMomentConst := by
    have hC := cutoffMomentConst_pos.le
    nlinarith [M.shellPrefix.delta_le_half]
  unfold oneStepRatioMinusOneEightBound oneStepRatioEightUniformConst
  calc
    cutoffMomentConst * Real.sqrt 8 * M.delta * Real.sqrt (h : ℝ) *
        Real.exp (cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ)) ≤
      cutoffMomentConst * Real.sqrt 8 * M.delta * Real.sqrt (h : ℝ) *
        Real.exp (4 * cutoffMomentConst) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg 8))
                hdelta.le)
              (Real.sqrt_nonneg _))
    _ = (cutoffMomentConst * Real.sqrt 8 *
        Real.exp (4 * cutoffMomentConst)) * M.delta *
          Real.sqrt (h : ℝ) := by ring

theorem oneStepMultiplierDerivativeMomentPayload_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    (oneStepRatioMinusOneEightBound M h + 1) *
        oneStepDerivativeGaugeEightBound M ≤
      oneStepMultiplierDerivativeFourthConst * M.delta := by
  rw [oneStepDerivativeGaugeEightBound_eq_const_mul]
  unfold oneStepMultiplierDerivativeFourthConst
  have hratio := oneStepRatioMinusOneEightBound_le_uniform M h hscale
  have hCg : 0 ≤ oneStepDerivativeGaugeConst := oneStepDerivativeGaugeConst_pos.le
  have hd : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  calc
    (oneStepRatioMinusOneEightBound M h + 1) *
        (oneStepDerivativeGaugeConst * M.delta) ≤
      (oneStepRatioEightUniformConst + 1) *
        (oneStepDerivativeGaugeConst * M.delta) :=
      mul_le_mul_of_nonneg_right (by linarith [hratio]) (mul_nonneg hCg hd)
    _ = (oneStepRatioEightUniformConst + 1) *
        oneStepDerivativeGaugeConst * M.delta := by ring

/-- Source-scale form of the differentiated-shell estimate: uniformly over
the parent center and evaluation point, its fixed-point random `L^4` norm is
`C delta`. -/
theorem eLpNorm_oneStepMultiplierDerivative_majorant_four_le_delta {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (z x : Vec d)
    (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          oneStepShellDerivativeGauge n h z omega)
      4 M.P.toMeasure ≤
        ENNReal.ofReal (oneStepMultiplierDerivativeFourthConst * M.delta) := by
  exact (eLpNorm_oneStepMultiplierDerivative_majorant_four_le M n h z x hh).trans
    (ENNReal.ofReal_le_ofReal
      (oneStepMultiplierDerivativeMomentPayload_le M h hscale))

/-- Literal fixed-point derivative estimate on a translated scale-`n` parent
cube.  This is the random estimate inserted into both the Dirichlet and
Neumann Calderon--Zygmund bounds. -/
theorem eLpNorm_parentScale_fderiv_oneStepMultiplierAt_four_le_delta {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (z x : Vec d)
    (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹)
    (hx : x - z ∈ openCubeSet (originCube d (n : ℤ))) :
    eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        (3 : ℝ) ^ n *
          ‖fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x‖)
      4 M.P.toMeasure ≤
        ENNReal.ofReal (oneStepMultiplierDerivativeFourthConst * M.delta) := by
  calc
    eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        (3 : ℝ) ^ n *
          ‖fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x‖)
        4 M.P.toMeasure ≤
      eLpNorm (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          oneStepShellDerivativeGauge n h z omega) 4 M.P.toMeasure := by
      have hstored : Measurable (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          oneStepShellDerivative n h omega x) := by
        unfold oneStepShellDerivative
        apply Finset.measurable_sum
        intro k _hk
        have hc : Continuous (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x) :=
          ContinuousEval.continuous_eval.comp
            ((continuous_subtype_val.snd).prodMk continuous_const)
        exact hc.measurable.comp (measurable_pi_apply k)
      have hderiv : Measurable (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x) := by
        simp_rw [(hasFDerivAt_oneStepMultiplierAt M n h _ x hh).fderiv]
        exact (Real.measurable_exp.comp
          ((measurable_cutoffShellSum (n + h) (n : ℤ) x).sub_const _)).smul hstored
      apply eLpNorm_mono_ae (hderiv.norm.const_mul ((3 : ℝ) ^ n)).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun omega => by
        have hlhs : 0 ≤ (3 : ℝ) ^ n *
            ‖fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x‖ :=
          mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)
        have hrhs : 0 ≤
            Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
              (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
              oneStepShellDerivativeGauge n h z omega :=
          mul_nonneg (Real.exp_pos _).le
            (oneStepShellDerivativeGauge_nonneg n h z omega)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlhs,
          abs_of_nonneg hrhs]
        exact parentScale_mul_norm_fderiv_oneStepMultiplierAt_le
          M n h z x omega hh hx
    _ ≤ ENNReal.ofReal (oneStepMultiplierDerivativeFourthConst * M.delta) :=
      eLpNorm_oneStepMultiplierDerivative_majorant_four_le_delta
        M n h z x hh hscale

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
