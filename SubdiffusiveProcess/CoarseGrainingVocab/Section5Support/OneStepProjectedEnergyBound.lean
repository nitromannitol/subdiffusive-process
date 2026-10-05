module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMollifiedHarmonic

@[expose] public section

/-!
# Quantitative one-step stationary projected energy

The exact stationary Helmholtz trace is combined with the fourth-order
one-shell cumulant estimate.  This is the stationary-energy payload of
`l.laplacian.corrector.energy`.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A dimension-independent numerical constant for the fourth-order
stationary projected-energy error. -/
def oneStepProjectedEnergyErrorConst : ℝ :=
  256 + 258 ^ 2 * Real.exp 33

theorem oneStepProjectedEnergyErrorConst_pos :
    0 < oneStepProjectedEnergyErrorConst := by
  unfold oneStepProjectedEnergyErrorConst
  positivity

/-- The exact suffix variance differs from its quadratic leading term only
at fourth order on the manuscript's one-step range. -/
theorem abs_suffixVariance_sub_two_tauSq_mul_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (h : ℕ)
    (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    |(oneShellCenteredExpTwoMoment M) ^ h - 1 -
        2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ)| ≤
      oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  let A : ℝ := (oneShellCenteredExpTwoMoment M) ^ h
  let T : ℝ := 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ)
  let x : ℝ := Real.log A
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  have hh1 : 1 ≤ (h : ℝ) := by exact_mod_cast hh
  have hdeltaH : M.delta * (h : ℝ) ≤ 1 := by
    have hscale' : (h : ℝ) ≤ 1 / M.delta := by
      simpa only [one_div] using hscale
    simpa only [mul_comm] using (le_div_iff₀ hdelta).mp hscale'
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 := by
    exact (tauSq_le_delta_sq M).trans
      (by
        have hlog : Real.log 2 / 2 ≤ 1 := by
          linarith [Real.log_two_lt_d9]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta))
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact mul_nonneg
      (mul_nonneg (by norm_num) M.G4.tauSq_pos.le) hh0
  have hT1 : T ≤ 1 := by
    have htauH := mul_le_mul_of_nonneg_right htau hh0
    have hdeltaSqH : M.delta ^ 2 * (h : ℝ) ≤ M.delta := by
      calc
        M.delta ^ 2 * (h : ℝ) = M.delta * (M.delta * (h : ℝ)) := by ring
        _ ≤ M.delta * 1 := mul_le_mul_of_nonneg_left hdeltaH hdelta.le
        _ = M.delta := mul_one _
    dsimp only [T]
    nlinarith
  have hAone : 1 ≤ A := by
    have hnonneg : 0 ≤ A - 1 := by
      rw [← integral_oneStepOriginMultiplier_sq M 0 h hh]
      exact integral_nonneg fun omega => sq_nonneg _
    linarith
  have hApos : 0 < A := zero_lt_one.trans_le hAone
  have hx0 : 0 ≤ x := by
    exact Real.log_nonneg hAone
  have hlogError : |x - T| ≤ 256 * M.delta ^ 4 * (h : ℝ) := by
    simpa only [A, T, x] using
      abs_log_oneShellCentered_pow_sub_two_tauSq_mul_le M h
  have hdeltaFourH : M.delta ^ 4 * (h : ℝ) ≤ M.delta ^ 2 * (h : ℝ) := by
    have hdeltaSq : M.delta ^ 2 ≤ 1 := by nlinarith [sq_nonneg M.delta]
    have hpow : M.delta ^ 4 ≤ M.delta ^ 2 := by
      nlinarith [sq_nonneg (M.delta ^ 2)]
    exact mul_le_mul_of_nonneg_right hpow hh0
  have hxLinear : x ≤ 258 * M.delta ^ 2 * (h : ℝ) := by
    rw [abs_le] at hlogError
    have htauH := mul_le_mul_of_nonneg_right htau hh0
    dsimp only [T] at hlogError
    nlinarith
  have hx33 : x ≤ 33 := by
    have hdeltaSq : M.delta ^ 2 ≤ 1 / 4 := by
      nlinarith [sq_nonneg (M.delta - 1 / 2)]
    have hdeltaCube : M.delta ^ 3 ≤ 1 / 8 := by
      calc
        M.delta ^ 3 = M.delta * M.delta ^ 2 := by ring
        _ ≤ (1 / 2 : ℝ) * (1 / 4 : ℝ) :=
          mul_le_mul hhalf hdeltaSq (sq_nonneg M.delta) (by norm_num)
        _ = 1 / 8 := by norm_num
    have hdeltaFourH : M.delta ^ 4 * (h : ℝ) ≤ 1 / 8 := by
      calc
        M.delta ^ 4 * (h : ℝ) =
            M.delta ^ 3 * (M.delta * (h : ℝ)) := by ring
        _ ≤ M.delta ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hdeltaH (by positivity)
        _ = M.delta ^ 3 := mul_one _
        _ ≤ 1 / 8 := hdeltaCube
    rw [abs_le] at hlogError
    calc
      x ≤ T + 256 * M.delta ^ 4 * (h : ℝ) := by linarith [hlogError.2]
      _ ≤ 1 + 256 * (1 / 8 : ℝ) :=
        add_le_add hT1 (by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hdeltaFourH
              (by norm_num : (0 : ℝ) ≤ 256))
      _ = 33 := by norm_num
  have hAexp : A = Real.exp x := by
    dsimp only [x]
    exact (Real.exp_log hApos).symm
  have hrem0 : 0 ≤ Real.exp x - 1 - x := by
    linarith [Real.add_one_le_exp x]
  have hexpSub : Real.exp x - 1 ≤ x * Real.exp x := by
    have hbase := Real.add_one_le_exp (-x)
    have hmul := mul_le_mul_of_nonneg_right hbase (Real.exp_pos x).le
    rw [← Real.exp_add] at hmul
    norm_num at hmul
    linarith
  have hrem : Real.exp x - 1 - x ≤ x ^ 2 * Real.exp x := by
    have hmul := mul_le_mul_of_nonneg_left hexpSub hx0
    nlinarith
  have hxSq : x ^ 2 ≤ 258 ^ 2 * M.delta ^ 4 * (h : ℝ) ^ 2 := by
    have hsq := pow_le_pow_left₀ hx0 hxLinear 2
    calc
      x ^ 2 ≤ (258 * M.delta ^ 2 * (h : ℝ)) ^ 2 := hsq
      _ = 258 ^ 2 * M.delta ^ 4 * (h : ℝ) ^ 2 := by ring
  have hremBound : |Real.exp x - 1 - x| ≤
      258 ^ 2 * Real.exp 33 * M.delta ^ 4 * (h : ℝ) ^ 2 := by
    rw [abs_of_nonneg hrem0]
    calc
      Real.exp x - 1 - x ≤ x ^ 2 * Real.exp x := hrem
      _ ≤ (258 ^ 2 * M.delta ^ 4 * (h : ℝ) ^ 2) * Real.exp x :=
        mul_le_mul_of_nonneg_right hxSq (Real.exp_pos _).le
      _ ≤ (258 ^ 2 * M.delta ^ 4 * (h : ℝ) ^ 2) * Real.exp 33 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx33) (by positivity)
      _ = 258 ^ 2 * Real.exp 33 * M.delta ^ 4 * (h : ℝ) ^ 2 := by ring
  have hlogErrorSq : |x - T| ≤
      256 * M.delta ^ 4 * (h : ℝ) ^ 2 := by
    calc
      |x - T| ≤ 256 * M.delta ^ 4 * (h : ℝ) := hlogError
      _ ≤ 256 * M.delta ^ 4 * (h : ℝ) ^ 2 := by
        have hfactor : 0 ≤ 256 * M.delta ^ 4 := by positivity
        nlinarith
  change |A - 1 - T| ≤ _
  rw [hAexp]
  have htriangle := abs_add_le (Real.exp x - 1 - x) (x - T)
  have hrewrite : Real.exp x - 1 - T =
      (Real.exp x - 1 - x) + (x - T) := by ring
  rw [hrewrite]
  calc
    |(Real.exp x - 1 - x) + (x - T)| ≤
        |Real.exp x - 1 - x| + |x - T| := htriangle
    _ ≤ (258 ^ 2 * Real.exp 33 + 256) * M.delta ^ 4 * (h : ℝ) ^ 2 := by
      nlinarith [hremBound, hlogErrorSq]
    _ = oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 := by
      unfold oneStepProjectedEnergyErrorConst
      ring

/-- Quantitative stationary Helmholtz energy with the manuscript's sharp
leading coefficient `2 tauSq h / d`. -/
theorem abs_oneStepProjectedEnergy_sub_two_tauSq_mul_div_dimension_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    |oneStepProjectedEnergy M n h p hh -
        2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ)| ≤
      oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  have hdNat : 2 ≤ d := M.shellPrefix.dimension
  have hd : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdNat.trans' (by omega)
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hd
  rw [oneStepProjectedEnergy_eq_suffixVariance_div_dimension_unit M n h p hh hp]
  rw [← sub_div, abs_div, abs_of_pos hdpos]
  have hscalar := abs_suffixVariance_sub_two_tauSq_mul_le M h hh hscale
  exact (div_le_iff₀ hdpos).2 (hscalar.trans (by
    have hnonneg : 0 ≤ oneStepProjectedEnergyErrorConst *
        M.delta ^ 4 * (h : ℝ) ^ 2 :=
      mul_nonneg
        (mul_nonneg oneStepProjectedEnergyErrorConst_pos.le
          (pow_nonneg M.shellPrefix.delta_pos.le 4))
        (sq_nonneg (h : ℝ))
    nlinarith))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
