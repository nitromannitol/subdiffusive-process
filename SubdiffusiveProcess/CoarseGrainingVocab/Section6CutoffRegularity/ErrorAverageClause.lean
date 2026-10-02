import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.AccumulatedErrorMeasurability
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.FluctuationOGamma
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.LogFreeMeanBound
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.WindowInputDischarge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.DepthGammaOne
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpMeanWindow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ResponseFirstMoment




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- `SubdiffusiveProcess.OGammaLE` is invariant under simultaneously dividing the observable and
the scale by a positive constant: the normalized quantity `A⁻¹ * max X 0` is
unchanged. -/
theorem ogammaLE_div_const {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {sigma A c : ℝ} {X : Omega → ℝ}
    (hc : 0 < c) (hX : SubdiffusiveProcess.OGammaLE mu sigma A X) :
    SubdiffusiveProcess.OGammaLE mu sigma (A / c) (fun omega ↦ X omega / c) := by
  have hkey : ∀ omega, (A / c)⁻¹ * max (X omega / c) 0 = A⁻¹ * max (X omega) 0 := by
    intro omega
    have hmax : max (X omega / c) 0 = max (X omega) 0 / c := by
      rw [div_eq_mul_inv, div_eq_mul_inv,
        max_mul_of_nonneg _ _ (inv_nonneg.mpr hc.le), zero_mul]
    rw [hmax, inv_div, div_eq_mul_inv, div_eq_mul_inv]
    rcases eq_or_ne A 0 with rfl | hA
    · simp
    · field_simp
  unfold SubdiffusiveProcess.OGammaLE at hX ⊢
  simpa only [hkey] using hX

theorem rpow_four_half : (4 : ℝ) ^ ((2 : ℝ)⁻¹) = 2 := by
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem div_le_div_of_le_nonneg {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.mpr hc)

/-- `(F * r) / (r * r) = F / r`, stated with the square generalized so the
rewrite does not reach inside `r` itself. -/
theorem mul_sqrt_div_self {F w r : ℝ} (hr : 0 < r) (hrw : r * r = w) :
    (F * r) / w = F / r := by
  rw [← hrw]
  field_simp

/-- The scale transfer, on plain real variables so that no tactic ever sees the
fluctuation scale as an atom. -/
theorem scale_transfer {Gen Ecoef Ccoef P r W : ℝ}
    (hGen : Gen ≤ (Ecoef * P) * r) (hcoef : 2 * Ecoef ≤ Ccoef) (hP : 0 ≤ P)
    (hr0 : 0 < r) (hrW : r * r = W) (hW0 : 0 < W) :
    (2 * Gen) / W ≤ (Ccoef * P) / r := by
  have h2E : 2 * (Ecoef * P) ≤ Ccoef * P := by nlinarith
  have h1 : 2 * Gen ≤ 2 * ((Ecoef * P) * r) := by linarith
  have h3 : 2 * ((Ecoef * P) * r) = (2 * (Ecoef * P)) * r := by ring
  have h2 : (2 * (Ecoef * P)) * r ≤ (Ccoef * P) * r :=
    mul_le_mul_of_nonneg_right h2E hr0.le
  have hnum : 2 * Gen ≤ (Ccoef * P) * r := by linarith
  refine (div_le_div_of_le_nonneg hnum hW0.le).trans_eq ?_
  exact mul_sqrt_div_self hr0 hrW

/-- **Conjunct (2) of the frozen finite-cutoff good-scale proposition.** -/
theorem exists_cutoff_regularity_error_average_clause (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, ∀ L : ℕ,
      ∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s → ∀ n m : ℕ, n ≤ m →
          ∀ z : Vec d,
            SubdiffusiveProcess.OGammaLE M.P.toMeasure 2
              (C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| /
                Real.sqrt ((m : ℝ) - (n : ℝ) + 1))
              (fun omega ↦ (∑ k ∈ Finset.Icc n m,
                accumulatedError M (some L) k z s omega) / ((m : ℝ) - (n : ℝ) + 1) -
                  C * s ^ (-7 / 2 : ℝ) * M.delta) := by
  obtain ⟨Krow, Crow, hKrow, hCrow, hrow⟩ :=
    exists_isBigOWith_gammaTwo_cutoffParameterizedResponseRow_of_budget (d := d)
  obtain ⟨Kmu, Cmu, hKmu, hCmu, hmu⟩ :=
    exists_integral_cutoffParameterizedResponseRow_le (d := d)
  have hCw : 0 < sharpErrorWindowConst d Crow := sharpErrorWindowConst_pos hCrow
  have hCm : 0 < logFreeMeanConst d Cmu := logFreeMeanConst_pos hCmu
  refine ⟨Krow + Kmu + logFreeMeanConst d Cmu + 2 * sharpErrorWindowConst d Crow,
    by positivity, ?_⟩
  set C : ℝ := Krow + Kmu + logFreeMeanConst d Cmu +
    2 * sharpErrorWindowConst d Crow with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  intro M L s hs hbudget n m hnm z
  obtain ⟨hs0, hs2⟩ := hs
  have hs1 : s ≤ 1 := hs2.trans (by norm_num)
  have hs8 : s / 8 ≤ 1 := by linarith
  -- model constants
  have hd0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg hd0 (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hlogpos : 0 < |Real.log M.delta| := abs_pos.mpr hlogNeg.ne
  have hLam : 0 < Real.sqrt |Real.log M.delta| := Real.sqrt_pos.mpr hlogpos
  have hbase : (0 : ℝ) < M.delta ^ 2 * |Real.log M.delta| := by positivity
  -- the window length
  have hnm1 : n ≤ m + 1 := by omega
  have hWeq : ((m + 1 - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) + 1 := by
    rw [Nat.cast_sub hnm1]
    push_cast
    ring
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hW0 : (0 : ℝ) < (m : ℝ) - (n : ℝ) + 1 := by linarith
  have hsqrtW0 : (0 : ℝ) < Real.sqrt ((m : ℝ) - (n : ℝ) + 1) :=
    Real.sqrt_pos.mpr hW0
  have hsqrtsq : Real.sqrt ((m : ℝ) - (n : ℝ) + 1) *
      Real.sqrt ((m : ℝ) - (n : ℝ) + 1) = (m : ℝ) - (n : ℝ) + 1 :=
    Real.mul_self_sqrt hW0.le
  -- budgets
  have hKrowB : Krow * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
    refine le_trans ?_ hbudget
    have hle : Krow ≤ C := by rw [hCdef]; linarith
    calc Krow * M.delta ^ 2 * |Real.log M.delta|
        = Krow * (M.delta ^ 2 * |Real.log M.delta|) := by ring
      _ ≤ C * (M.delta ^ 2 * |Real.log M.delta|) :=
          mul_le_mul_of_nonneg_right hle hbase.le
      _ = C * M.delta ^ 2 * |Real.log M.delta| := by ring
  have hKmuB : Kmu * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
    refine le_trans ?_ hbudget
    have hle : Kmu ≤ C := by rw [hCdef]; linarith
    calc Kmu * M.delta ^ 2 * |Real.log M.delta|
        = Kmu * (M.delta ^ 2 * |Real.log M.delta|) := by ring
      _ ≤ C * (M.delta ^ 2 * |Real.log M.delta|) :=
          mul_le_mul_of_nonneg_right hle hbase.le
      _ = C * M.delta ^ 2 * |Real.log M.delta| := by ring
  -- the response row scale and first moment
  set A : ℝ := Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s with hAdef
  have hA : 0 < A := by
    rw [hAdef]
    exact mul_pos (Real.exp_pos 1)
      (cutoffParameterizedResponseGammaScale_pos M hCrow hs0)
  have hrow' := hrow M s hs0 hs1 hKrowB L
  have hmu' := hmu M s hs0 hs1 hKmuB L
  -- the fluctuation in expectation form
  have hGenpos : 0 < cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
      M s A n m (sharpFieldLowWindowScale M s) :=
    cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_pos M hs0 hA hnm
      (sharpFieldLowWindowScale_pos M hs0)
  have hfluctO := ogammaLE_cutoffParameterizedAccumulatedErrorWindowFluctuation_sharp
    M L hs0 hs1 z hnm hA hrow' hGenpos
  rw [rpow_four_half] at hfluctO
  have hdiv := ogammaLE_div_const (c := (m : ℝ) - (n : ℝ) + 1) hW0 hfluctO
  -- the observable is measurable
  have hobs : Measurable (fun omega : PotentialSample d ↦
      (∑ k ∈ Finset.Icc n m, accumulatedError M (some L) k z s omega) /
          ((m : ℝ) - (n : ℝ) + 1) -
        C * s ^ (-7 / 2 : ℝ) * M.delta) :=
    ((Finset.measurable_sum _ fun k _ ↦
      measurable_accumulatedError M (some L) k z s).div_const _).sub_const _
  -- the pathwise comparison
  have hae := ae_sum_cutoffParameterizedAccumulatedError_le_sharp_mean
    M L hs0 hs1 z hnm hmu'
  have hmeanb := cutoffParameterizedAccumulatedErrorWindowSharpMeanBound_le
    (M := M) (Cr := Cmu) hs0 hs1 hCmu.le le_rfl n m
  have hQ0 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) * M.delta :=
    mul_nonneg (Real.rpow_pos_of_pos hs0 _).le hd0.le
  have hCmC : logFreeMeanConst d Cmu ≤ C := by rw [hCdef]; linarith
  have hle : ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m, accumulatedError M (some L) k z s omega) /
            ((m : ℝ) - (n : ℝ) + 1) -
          C * s ^ (-7 / 2 : ℝ) * M.delta ≤
        cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m omega /
          ((m : ℝ) - (n : ℝ) + 1) := by
    filter_upwards [hae] with omega homega
    have hkey : (∑ k ∈ Finset.Icc n m, accumulatedError M (some L) k z s omega) ≤
        cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m omega +
          (C * s ^ (-7 / 2 : ℝ) * M.delta) * ((m : ℝ) - (n : ℝ) + 1) := by
      have hmb := hmeanb
      rw [hWeq] at hmb
      have hmono : ((m : ℝ) - (n : ℝ) + 1) *
          (logFreeMeanConst d Cmu * s ^ (-7 / 2 : ℝ) * M.delta) ≤
          (C * s ^ (-7 / 2 : ℝ) * M.delta) * ((m : ℝ) - (n : ℝ) + 1) := by
        have h1 : logFreeMeanConst d Cmu * (s ^ (-7 / 2 : ℝ) * M.delta) ≤
            C * (s ^ (-7 / 2 : ℝ) * M.delta) :=
          mul_le_mul_of_nonneg_right hCmC hQ0
        have h2 := mul_le_mul_of_nonneg_left h1 hW0.le
        calc ((m : ℝ) - (n : ℝ) + 1) *
              (logFreeMeanConst d Cmu * s ^ (-7 / 2 : ℝ) * M.delta)
            = ((m : ℝ) - (n : ℝ) + 1) *
              (logFreeMeanConst d Cmu * (s ^ (-7 / 2 : ℝ) * M.delta)) := by ring
          _ ≤ ((m : ℝ) - (n : ℝ) + 1) * (C * (s ^ (-7 / 2 : ℝ) * M.delta)) := h2
          _ = (C * s ^ (-7 / 2 : ℝ) * M.delta) * ((m : ℝ) - (n : ℝ) + 1) := by ring
      linarith
    have hstep : (∑ k ∈ Finset.Icc n m, accumulatedError M (some L) k z s omega) /
          ((m : ℝ) - (n : ℝ) + 1) ≤
        (cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m omega +
          (C * s ^ (-7 / 2 : ℝ) * M.delta) * ((m : ℝ) - (n : ℝ) + 1)) /
            ((m : ℝ) - (n : ℝ) + 1) := by
      exact div_le_div_of_le_nonneg hkey hW0.le
    have hsplit : (cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m omega +
          (C * s ^ (-7 / 2 : ℝ) * M.delta) * ((m : ℝ) - (n : ℝ) + 1)) /
            ((m : ℝ) - (n : ℝ) + 1) =
        cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m omega /
            ((m : ℝ) - (n : ℝ) + 1) + C * s ^ (-7 / 2 : ℝ) * M.delta := by
      field_simp
    linarith [hstep, hsplit.le, hsplit.ge]
  -- the scale comparison
  have hGenle := cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_sharp_le
    (M := M) (Crow := Crow) hCrow hs0 hs1 hnm
  have hscale : (2 * cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
        M s A n m (sharpFieldLowWindowScale M s)) / ((m : ℝ) - (n : ℝ) + 1) ≤
      C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| /
        Real.sqrt ((m : ℝ) - (n : ℝ) + 1) := by
    have hGen' : cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
        M s A n m (sharpFieldLowWindowScale M s) ≤
        (sharpErrorWindowConst d Crow *
          (s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta|)) *
          Real.sqrt ((m : ℝ) - (n : ℝ) + 1) := by
      have hg := hGenle
      unfold errorWindowScale at hg
      rw [hWeq] at hg
      exact hg.trans (le_of_eq (by ring))
    have hCwC : 2 * sharpErrorWindowConst d Crow ≤ C := by rw [hCdef]; linarith
    have hPQ : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) * M.delta *
        Real.sqrt |Real.log M.delta| := by positivity
    have hres := scale_transfer hGen' hCwC hPQ hsqrtW0 hsqrtsq hW0
    refine hres.trans_eq ?_
    ring
  refine ogammaLE_mono_scale (by norm_num) (by positivity) hscale hobs ?_
  exact ogammaLE_mono_observable (by norm_num) (by positivity) hobs hle hdiv

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
