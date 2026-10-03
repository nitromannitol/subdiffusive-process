module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedEnergyComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

@[expose] public section




open MeasureTheory Homogenization Homogenization.IndependentSums
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The centered logarithmic one-step shell. -/
def oneStepCenteredShellAt {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  cutoffShellSum (n + h) (n : ℤ) x omega -
    (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P

/-- The forcing left after subtracting the uncentered linear shell from the
literal lognormal multiplier. -/
def oneStepExpRemainderAt {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  Real.exp (oneStepCenteredShellAt M n h x omega) - 1 -
    cutoffShellSum (n + h) (n : ℤ) x omega

theorem oneStepMultiplierAt_eq_shell_add_remainder {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepMultiplierAt M n h x omega =
      cutoffShellSum (n + h) (n : ℤ) x omega +
        oneStepExpRemainderAt M n h x omega := by
  rw [← oneStepMultiplierContinuousMap_apply M n h omega x hh]
  change Real.exp
      (cutoffShellSum (n + h) (n : ℤ) x omega -
        (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1 = _
  simp only [oneStepExpRemainderAt, oneStepCenteredShellAt]
  ring

/-- Global pointwise envelope for the nonlinear forcing remainder. -/
theorem abs_oneStepExpRemainderAt_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    |oneStepExpRemainderAt M n h x omega| ≤
      ((oneStepCenteredShellAt M n h x omega) ^ 2 / 2) *
          Real.exp |oneStepCenteredShellAt M n h x omega| +
        (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
  let H := oneStepCenteredShellAt M n h x omega
  let b := (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hb0 : 0 ≤ b := mul_nonneg (Nat.cast_nonneg h) M.G4.tauSq_pos.le
  have hrewrite : oneStepExpRemainderAt M n h x omega =
      (Real.exp H - 1 - H) - b := by
    dsimp only [oneStepExpRemainderAt, oneStepCenteredShellAt, H, b]
    ring
  rw [hrewrite]
  calc
    |(Real.exp H - 1 - H) - b| ≤ |Real.exp H - 1 - H| + |b| := abs_sub _ _
    _ ≤ (H ^ 2 / 2) * Real.exp |H| + b := by
      rw [abs_of_nonneg hb0]
      exact add_le_add
        (abs_exp_sub_one_sub_id_le_half_sq_mul_exp_abs H) le_rfl

/-- `L^q` norm of the absolute exponential of a deterministically shifted
weak-subgaussian random variable. -/
theorem eLpNorm_exp_abs_sub_const_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A q b : ℝ}
    (hA : 0 < A) (hq : 1 ≤ q) (hXm : AEMeasurable X mu)
    (hX : IsBigO mu (gammaSigma 2) X A) :
    eLpNorm (fun omega ↦ Real.exp |X omega - b|) (ENNReal.ofReal q) mu ≤
      (ENNReal.ofReal
        (4 * Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|))) ^ q⁻¹ := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  obtain ⟨hInt, hBound⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.integral_exp_abs_sub_const_le
    (mu := mu) (X := X) (A := A) (q := q) (b := b)
    hA hq0.le hXm hX
  let F : Omega → ℝ := fun omega ↦ Real.exp |X omega - b|
  have hFm : AEStronglyMeasurable F mu :=
    (Real.measurable_exp.comp_aemeasurable (hXm.sub_const b).norm)
      |>.aestronglyMeasurable
  have hpow : Integrable (fun omega ↦ ‖F omega‖ ^ q) mu := by
    convert hInt using 1
    funext omega
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hmem : MemLp F (ENNReal.ofReal q) mu := by
    apply (integrable_norm_rpow_iff hFm (by positivity) ENNReal.ofReal_ne_top).1
    simpa only [ENNReal.toReal_ofReal hq0.le] using! hpow
  rw [hmem.eLpNorm_eq_integral_rpow_norm
    (by positivity) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hq0.le]
  have hbase : ∫ omega, ‖F omega‖ ^ q ∂mu ≤
      4 * Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|) := by
    have heq : (fun omega ↦ ‖F omega‖ ^ q) =
        (fun omega ↦ Real.exp (q * |X omega - b|)) := by
      funext omega
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [heq]
    exact hBound
  have hroot := Real.rpow_le_rpow
    (integral_nonneg fun omega ↦ Real.rpow_nonneg (norm_nonneg _) q)
    hbase (inv_nonneg.mpr hq0.le)
  exact (ENNReal.ofReal_le_ofReal hroot).trans_eq (by
    rw [ENNReal.ofReal_rpow_of_pos (by positivity :
      0 < 4 * Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|))])

/-- Explicit fourth-moment majorant for the nonlinear forcing remainder. -/
def oneStepExpRemainderFourBound {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ) : ℝ≥0∞ :=
  let A := cutoffGammaConst * Real.sqrt (h : ℝ) * M.delta
  let b := (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  let H16 := gammaMomentConst 2 * Real.sqrt 16 * (A + |b|)
  let E8 := (ENNReal.ofReal
    (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^ (8 : ℝ)⁻¹
  (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal H16) ^ (2 : ℕ) * E8 +
    ENNReal.ofReal b

/-- Universal constant in the one-step fourth-moment remainder estimate. -/
noncomputable def oneStepExpRemainderConst : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal
        (gammaMomentConst 2 * Real.sqrt 16 * (cutoffGammaConst + 1)) ^ 2 *
      (ENNReal.ofReal
        (4 * Real.exp (32 * cutoffGammaConst ^ 2 + 8))) ^ (8 : ℝ)⁻¹ +
    1

/-- On the manuscript's one-step range, the explicit remainder majorant has
the sharp `delta² h` scale. -/
theorem oneStepExpRemainderFourBound_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ)
    (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    oneStepExpRemainderFourBound M h ≤
      oneStepExpRemainderConst * ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by
  let delta : ℝ := M.delta
  let tau : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  let y : ℝ := delta * Real.sqrt (h : ℝ)
  have hdelta : 0 < delta := M.shellPrefix.delta_pos
  have hdelta1 : delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
  have hhreal : (0 : ℝ) < h := by exact_mod_cast hh
  have hsqrth : 0 ≤ Real.sqrt (h : ℝ) := Real.sqrt_nonneg _
  have hysq : y ^ 2 = delta ^ 2 * (h : ℝ) := by
    dsimp only [y]
    rw [mul_pow, Real.sq_sqrt hhreal.le]
  have hy0 : 0 ≤ y := mul_nonneg hdelta.le hsqrth
  have hy1 : y ≤ 1 := by
    have hmul : delta * (h : ℝ) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hscale hdelta.le
      simpa [delta, hdelta.ne'] using! this
    have hsq : y ^ 2 ≤ 1 := by
      rw [hysq]
      nlinarith
    nlinarith
  have hysq_le : y ^ 2 ≤ y := by nlinarith
  have htau0 : 0 ≤ tau := M.G4.tauSq_pos.le
  have htau : tau ≤ delta ^ 2 := by
    have hlog : Real.log 2 / 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    simpa only [tau, delta, one_mul] using! (tauSq_le_delta_sq M).trans
      (mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta))
  have hb0 : 0 ≤ (h : ℝ) * tau := mul_nonneg hhreal.le htau0
  have hb_le_y2 : (h : ℝ) * tau ≤ y ^ 2 := by
    rw [hysq]
    simpa only [mul_comm] using! mul_le_mul_of_nonneg_left htau hhreal.le
  have hb_le_y : (h : ℝ) * tau ≤ y := hb_le_y2.trans hysq_le
  have hA0 : 0 ≤ cutoffGammaConst * Real.sqrt (h : ℝ) * delta := by
    exact mul_nonneg
      (mul_nonneg cutoffGammaConst_pos.le hsqrth) hdelta.le
  have hA_le : cutoffGammaConst * Real.sqrt (h : ℝ) * delta ≤
      cutoffGammaConst := by
    calc
      cutoffGammaConst * Real.sqrt (h : ℝ) * delta = cutoffGammaConst * y := by
        dsimp only [y]
        ring
      _ ≤ cutoffGammaConst * 1 :=
        mul_le_mul_of_nonneg_left hy1 cutoffGammaConst_pos.le
      _ = cutoffGammaConst := mul_one _
  have hsum :
      cutoffGammaConst * Real.sqrt (h : ℝ) * delta + |(h : ℝ) * tau| ≤
        (cutoffGammaConst + 1) * y := by
    rw [abs_of_nonneg hb0]
    calc
      cutoffGammaConst * Real.sqrt (h : ℝ) * delta + (h : ℝ) * tau ≤
          cutoffGammaConst * y + y := by
        apply add_le_add
        · have heq : cutoffGammaConst * Real.sqrt (h : ℝ) * delta =
              cutoffGammaConst * y := by
            dsimp only [y]
            ring
          exact heq.le
        · exact hb_le_y
      _ = (cutoffGammaConst + 1) * y := by ring
  have hexponent :
      8 ^ 2 * (cutoffGammaConst * Real.sqrt (h : ℝ) * delta) ^ 2 / 2 +
          8 * |(h : ℝ) * tau| ≤
        32 * cutoffGammaConst ^ 2 + 8 := by
    rw [abs_of_nonneg hb0]
    have hb1 : (h : ℝ) * tau ≤ 1 := hb_le_y.trans hy1
    nlinarith [sq_nonneg
      (cutoffGammaConst - cutoffGammaConst * Real.sqrt (h : ℝ) * delta),
      mul_self_le_mul_self hA0 hA_le]
  have hsum0 : 0 ≤
      gammaMomentConst 2 * Real.sqrt 16 *
        (cutoffGammaConst * Real.sqrt (h : ℝ) * delta + |(h : ℝ) * tau|) := by
    exact mul_nonneg
      (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _))
      (add_nonneg hA0 (abs_nonneg _))
  have hcommon0 : 0 ≤
      gammaMomentConst 2 * Real.sqrt 16 * (cutoffGammaConst + 1) := by
    exact mul_nonneg
      (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _))
      (by linarith [cutoffGammaConst_pos])
  have hH :
      gammaMomentConst 2 * Real.sqrt 16 *
          (cutoffGammaConst * Real.sqrt (h : ℝ) * delta + |(h : ℝ) * tau|) ≤
        (gammaMomentConst 2 * Real.sqrt 16 * (cutoffGammaConst + 1)) * y := by
    calc
      _ ≤ gammaMomentConst 2 * Real.sqrt 16 * ((cutoffGammaConst + 1) * y) :=
        mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _))
      _ = _ := by ring
  have hExp :
      (ENNReal.ofReal
        (4 * Real.exp
          (8 ^ 2 * (cutoffGammaConst * Real.sqrt (h : ℝ) * delta) ^ 2 / 2 +
            8 * |(h : ℝ) * tau|))) ^ (8 : ℝ)⁻¹ ≤
      (ENNReal.ofReal
        (4 * Real.exp (32 * cutoffGammaConst ^ 2 + 8))) ^ (8 : ℝ)⁻¹ := by
    gcongr
  dsimp only [delta, tau] at hysq hb_le_y2 hH hExp
  have hyOf : ENNReal.ofReal y ^ (2 : ℕ) =
      ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by
    rw [← ENNReal.ofReal_pow hy0, hysq]
  have hbOf : ENNReal.ofReal ((h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
      ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    have hbRaw := mul_le_mul_of_nonneg_left htau hhreal.le
    simpa only [tau, delta, mul_comm] using! hbRaw
  have hHof :
      ENNReal.ofReal
          (gammaMomentConst 2 * Real.sqrt 16 *
            (cutoffGammaConst * Real.sqrt (h : ℝ) * M.delta +
              |(h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ (2 : ℕ) ≤
        ENNReal.ofReal
            (gammaMomentConst 2 * Real.sqrt 16 * (cutoffGammaConst + 1)) ^ (2 : ℕ) *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by
    calc
      _ ≤ ENNReal.ofReal
          ((gammaMomentConst 2 * Real.sqrt 16 * (cutoffGammaConst + 1)) * y) ^
            (2 : ℕ) := by
        gcongr
      _ = _ := by
        rw [ENNReal.ofReal_mul hcommon0, mul_pow, hyOf]
  dsimp only [oneStepExpRemainderFourBound, oneStepExpRemainderConst]
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal
            (gammaMomentConst 2 * Real.sqrt 16 * (cutoffGammaConst + 1)) ^ 2 *
            ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) *
          (ENNReal.ofReal
            (4 * Real.exp (32 * cutoffGammaConst ^ 2 + 8))) ^ (8 : ℝ)⁻¹ +
        ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by
      apply add_le_add
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hHof (zero_le)
        · exact hExp
        · exact zero_le
        · exact zero_le
      · exact hbOf
    _ = ((2 : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal
            (gammaMomentConst 2 * Real.sqrt 16 * (cutoffGammaConst + 1)) ^ 2 *
          (ENNReal.ofReal
            (4 * Real.exp (32 * cutoffGammaConst ^ 2 + 8))) ^ (8 : ℝ)⁻¹ + 1) *
        ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by ring

/-- Fixed-point `L^4` estimate for the forcing remainder. -/
theorem eLpNorm_oneStepExpRemainderAt_four_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (hh : 0 < h) :
    eLpNorm (oneStepExpRemainderAt M n h x) 4 M.P.toMeasure ≤
      oneStepExpRemainderFourBound M h := by
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := cutoffShellSum (n + h) (n : ℤ) x
  let A : ℝ := cutoffGammaConst * Real.sqrt (h : ℝ) * M.delta
  let b : ℝ := (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  let H : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦ X omega - b
  let f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦ |H omega| ^ (2 : ℝ)
  let g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦ Real.exp |H omega|
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos cutoffGammaConst_pos
      (Real.sqrt_pos.mpr (by positivity))) M.shellPrefix.delta_pos
  have hXmeas : AEMeasurable X M.P.toMeasure :=
    (measurable_cutoffShellSum (n + h) (n : ℤ) x).aemeasurable
  have hXgamma : IsBigO M.P.toMeasure (gammaSigma 2) X A := by
    have hraw := isBigO_gammaTwo_cutoffShellSum_sourceScale
      M (n + h) (n : ℤ) x (by omega) (by exact_mod_cast Nat.lt_add_of_pos_right hh)
    have hdiff : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
      push_cast
      ring
    simpa only [X, A, hdiff] using! hraw
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg (Nat.cast_nonneg h) M.G4.tauSq_pos.le
  have hHmeas : AEStronglyMeasurable H M.P.toMeasure :=
    (hXmeas.sub_const b).aestronglyMeasurable
  have hHaem : AEMeasurable H M.P.toMeasure := hXmeas.sub_const b
  have hH16 : eLpNorm H 16 M.P.toMeasure ≤
      ENNReal.ofReal (gammaMomentConst 2 * Real.sqrt 16 * (A + |b|)) := by
    simpa only [H, ENNReal.ofReal_ofNat] using!
      SubdiffusiveProcess.CoarseGrainingVocab.eLpNorm_le_of_isBigO_gammaTwo
      (A := A + |b|) (p := 16)
      (add_pos_of_pos_of_nonneg hA (abs_nonneg b)) (by norm_num)
      (hXmeas.sub_const b)
      (by simpa only [H] using!
        SubdiffusiveProcess.CoarseGrainingVocab.isBigO_gammaTwo_sub_const hXgamma)
  have hfNorm : eLpNorm f 8 M.P.toMeasure =
      eLpNorm H 16 M.P.toMeasure ^ (2 : ℝ) := by
    have hr := eLpNorm_norm_rpow (μ := M.P.toMeasure) H hHmeas
      (p := (8 : ℝ≥0∞)) (q := (2 : ℝ)) (by norm_num)
    convert hr using 1
    all_goals
      norm_num only [f, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_ofNat,
        ENNReal.rpow_two]
  have hgNorm : eLpNorm g 8 M.P.toMeasure ≤
      (ENNReal.ofReal
        (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^ (8 : ℝ)⁻¹ := by
    simpa only [g, H, ENNReal.ofReal_ofNat] using!
      eLpNorm_exp_abs_sub_const_le
        (mu := M.P.toMeasure) (X := X) (A := A) (q := 8) (b := b)
        hA (by norm_num) hXmeas hXgamma
  letI : ENNReal.HolderTriple (8 : ℝ≥0∞) (8 : ℝ≥0∞) (4 : ℝ≥0∞) :=
    { inv_add_inv_eq_inv := by
        rw [← two_mul]
        have h8 : (8 : ℝ≥0∞) = 2 * 4 := by norm_num
        rw [h8, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul] }
  have hfg : eLpNorm (fun omega ↦ f omega * g omega) 4 M.P.toMeasure ≤
      eLpNorm f 8 M.P.toMeasure * eLpNorm g 8 M.P.toMeasure := by
    simpa only [f, g, Real.norm_eq_abs, one_mul, Function.comp_def, ENNReal.coe_one, Real.rpow_two] using! eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := (8 : ℝ≥0∞)) (q := (8 : ℝ≥0∞)) (r := (4 : ℝ≥0∞))
      (fun a c : ℝ ↦ a * c) 1 (by fun_prop)
      ((hHaem.norm.pow_const 2).aestronglyMeasurable)
      ((Real.measurable_exp.comp_aemeasurable hHaem.norm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega ↦ by simp)

  have hmain : eLpNorm (fun omega ↦
      ((H omega) ^ 2 / 2) * Real.exp |H omega|) 4 M.P.toMeasure ≤
      (2 : ℝ≥0∞)⁻¹ *
        (ENNReal.ofReal (gammaMomentConst 2 * Real.sqrt 16 * (A + |b|))) ^
          (2 : ℕ) *
        ((ENNReal.ofReal
          (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^ (8 : ℝ)⁻¹) := by
    have hscale : (fun omega ↦ ((H omega) ^ 2 / 2) * Real.exp |H omega|) =
        (2 : ℝ)⁻¹ • (fun omega ↦ f omega * g omega) := by
      funext omega
      dsimp only [f, g]
      rw [Pi.smul_apply, smul_eq_mul, Real.rpow_two, sq_abs]
      ring
    rw [hscale, eLpNorm_const_smul]
    have hc : ‖(2 : ℝ)⁻¹‖ₑ = (2 : ℝ≥0∞)⁻¹ := by
      rw [Real.enorm_eq_ofReal (by positivity : 0 ≤ (2 : ℝ)⁻¹),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hc]
    calc
      (2 : ℝ≥0∞)⁻¹ *
          eLpNorm (fun omega ↦ f omega * g omega) 4 M.P.toMeasure ≤
        (2 : ℝ≥0∞)⁻¹ *
          (eLpNorm f 8 M.P.toMeasure * eLpNorm g 8 M.P.toMeasure) := by
            gcongr
      _ ≤ (2 : ℝ≥0∞)⁻¹ *
          ((ENNReal.ofReal
            (gammaMomentConst 2 * Real.sqrt 16 * (A + |b|))) ^ (2 : ℝ) *
            ((ENNReal.ofReal
              (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^ (8 : ℝ)⁻¹)) := by
        gcongr
        rw [hfNorm]
        exact ENNReal.rpow_le_rpow hH16 (by norm_num)
      _ = _ := by
        norm_num [ENNReal.rpow_two, pow_two, mul_assoc]
  have htargetMeas : AEStronglyMeasurable
      (oneStepExpRemainderAt M n h x) M.P.toMeasure := by
    exact ((Real.measurable_exp.comp
      ((measurable_cutoffShellSum (n + h) (n : ℤ) x).sub_const _)).sub_const _
      |>.sub (measurable_cutoffShellSum (n + h) (n : ℤ) x)).aestronglyMeasurable
  have hmajorMeas : AEStronglyMeasurable (fun omega ↦
      ((H omega) ^ 2 / 2) * Real.exp |H omega|) M.P.toMeasure := by
    exact (((hHaem.pow_const 2).div_const 2).mul
      (Real.measurable_exp.comp_aemeasurable hHaem.norm)).aestronglyMeasurable
  have hconstMeas : AEStronglyMeasurable (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ b) M.P.toMeasure :=
    aestronglyMeasurable_const
  have htri := eLpNorm_add_le (μ := M.P.toMeasure)
    (f := fun omega => ((H omega) ^ 2 / 2) * Real.exp |H omega|)
    (g := fun _ => b)
    (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hmono : eLpNorm (oneStepExpRemainderAt M n h x) 4 M.P.toMeasure ≤
      eLpNorm (fun omega ↦
        ((H omega) ^ 2 / 2) * Real.exp |H omega| + b) 4 M.P.toMeasure := by
    apply eLpNorm_mono_ae htargetMeas
    filter_upwards with omega
    have hpoint := abs_oneStepExpRemainderAt_le M n h x omega
    change |oneStepExpRemainderAt M n h x omega| ≤
      |((H omega) ^ 2 / 2) * Real.exp |H omega| + b|
    rw [abs_of_nonneg (add_nonneg
      (mul_nonneg (by positivity) (Real.exp_pos _).le) hb0)]
    simpa only [H, X, b, oneStepCenteredShellAt] using! hpoint
  calc
    eLpNorm (oneStepExpRemainderAt M n h x) 4 M.P.toMeasure ≤
        eLpNorm (fun omega ↦
          ((H omega) ^ 2 / 2) * Real.exp |H omega| + b) 4 M.P.toMeasure := hmono
    _ ≤ eLpNorm (fun omega ↦
          ((H omega) ^ 2 / 2) * Real.exp |H omega|) 4 M.P.toMeasure +
        eLpNorm (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ b) 4 M.P.toMeasure := htri
    _ ≤ (2 : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal (gammaMomentConst 2 * Real.sqrt 16 * (A + |b|))) ^
            (2 : ℕ) *
          ((ENNReal.ofReal
            (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^ (8 : ℝ)⁻¹) +
        ENNReal.ofReal b := by
      apply add_le_add hmain
      rw [eLpNorm_const b (by norm_num) (NeZero.ne M.P.toMeasure)]
      simp [Real.enorm_eq_ofReal hb0]
    _ = oneStepExpRemainderFourBound M h := by
      simp only [oneStepExpRemainderFourBound, A, b]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
