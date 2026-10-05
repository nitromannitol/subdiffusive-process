module

public import SubdiffusiveProcess.Rosenthal.Centered

@[expose] public section

/-!
# Moment bound for sums of nonnegative independent variables

For independent `Y_i ≥ 0` with `Y_i ≤ Mx` and `r ≥ 1`, with `A = ∑ Y_i`, `T = ‖A‖_r`, `m = ‖Mx‖_r`:
`T ≤ ∑ E Y_i + 2 K_r m^{1/2} T^{1/2}`  (centering, `Centered.lintegral_centered_root_le` for `Y`,
`∑ Y_i² ≤ Mx · A`, Cauchy–Schwarz).
-/

namespace SubdiffusiveProcess.Rosenthal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem nonneg_step {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ι → Ω → ℝ}
    (hYm : ∀ i, Measurable (Y i)) (hYnn : ∀ i ω, 0 ≤ Y i ω) (hYind : iIndepFun Y μ)
    {r : ℝ} (hr : 1 ≤ r) (hYint : ∀ i, Integrable (fun ω => |Y i ω| ^ r) μ)
    {Mx : Ω → ℝ} (hMm : Measurable Mx) (hM0 : ∀ ω, 0 ≤ Mx ω) (hYM : ∀ i ω, Y i ω ≤ Mx ω) :
    (∫⁻ ω, ENNReal.ofReal ((∑ i, Y i ω) ^ r) ∂μ) ^ (1 / r) ≤
      ENNReal.ofReal (∑ i, ∫ ω, Y i ω ∂μ) +
        ENNReal.ofReal (khintchineConst r) * 2 *
          (((∫⁻ ω, ENNReal.ofReal (Mx ω ^ r) ∂μ) ^ (1 / r)) ^ (1 / 2 : ℝ) *
          ((∫⁻ ω, ENNReal.ofReal ((∑ i, Y i ω) ^ r) ∂μ) ^ (1 / r)) ^ (1 / 2 : ℝ)) := by
  have hr0 : 0 < r := by linarith
  set A : Ω → ℝ := fun ω => ∑ i, Y i ω with hAdef
  set C : Ω → ℝ := fun ω => ∑ i, (Y i ω - ∫ x, Y i x ∂μ) with hCdef
  set μ0 : ℝ := ∑ i, ∫ ω, Y i ω ∂μ with hμ0def
  have hμ0 : 0 ≤ μ0 := Finset.sum_nonneg (fun i _ => integral_nonneg (hYnn i))
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => Finset.sum_nonneg (fun i _ => hYnn i ω)
  have hAC : ∀ ω, A ω = C ω + μ0 := by
    intro ω
    simp only [hAdef, hCdef, hμ0def, Finset.sum_sub_distrib]
    ring
  have hAm : Measurable A := Finset.measurable_sum _ (fun i _ => hYm i)
  have hCm : Measurable C := Finset.measurable_sum _ (fun i _ => (hYm i).sub_const _)
  -- Step (ii): centering
  have hpt : ∀ ω, ENNReal.ofReal (A ω ^ r) ≤ (ENNReal.ofReal |C ω| + ENNReal.ofReal μ0) ^ r := by
    intro ω
    have h1 : A ω ≤ |C ω| + μ0 := by rw [hAC]; linarith [le_abs_self (C ω)]
    calc ENNReal.ofReal (A ω ^ r) ≤ ENNReal.ofReal ((|C ω| + μ0) ^ r) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hA0 ω) h1 hr0.le)
      _ = (ENNReal.ofReal (|C ω| + μ0)) ^ r :=
          (ENNReal.ofReal_rpow_of_nonneg (by positivity) hr0.le).symm
      _ = _ := by rw [ENNReal.ofReal_add (abs_nonneg _) hμ0]
  have hFm : Measurable (fun ω => ENNReal.ofReal |C ω|) := ENNReal.measurable_ofReal.comp hCm.abs
  have hmink := ENNReal.lintegral_Lp_add_le (μ := μ) (f := fun ω => ENNReal.ofReal |C ω|)
    (g := fun _ => ENNReal.ofReal μ0) hFm.aemeasurable aemeasurable_const hr
  have hG : (∫⁻ _ : Ω, (ENNReal.ofReal μ0) ^ r ∂μ) ^ (1 / r) = ENNReal.ofReal μ0 := by
    rw [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne',
      ENNReal.rpow_one]
  have hF : (∫⁻ ω, (ENNReal.ofReal |C ω|) ^ r ∂μ) = ∫⁻ ω, ENNReal.ofReal (|C ω| ^ r) ∂μ :=
    lintegral_congr (fun ω => ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr0.le)
  -- Step (iii): Khintchine for the centered sum
  have hcen := lintegral_centered_root_le (μ := μ) hYm hYind hr hYint
  -- Step (iv): square function
  have hpt2 : ∀ ω, ENNReal.ofReal ((∑ i, Y i ω ^ 2) ^ (r / 2)) ≤
      ENNReal.ofReal (Mx ω ^ (r / 2)) * ENNReal.ofReal (A ω ^ (r / 2)) := by
    intro ω
    have h1 : ∑ i, Y i ω ^ 2 ≤ Mx ω * A ω := by
      simp only [hAdef, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => by
        have := hYM i ω
        have := hYnn i ω
        nlinarith)
    calc ENNReal.ofReal ((∑ i, Y i ω ^ 2) ^ (r / 2))
        ≤ ENNReal.ofReal ((Mx ω * A ω) ^ (r / 2)) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => sq_nonneg _)) h1
            (by linarith))
      _ = ENNReal.ofReal (Mx ω ^ (r / 2) * A ω ^ (r / 2)) := by
          rw [Real.mul_rpow (hM0 ω) (hA0 ω)]
      _ = _ := ENNReal.ofReal_mul (Real.rpow_nonneg (hM0 ω) _)
  have hMm' : Measurable (fun ω => ENNReal.ofReal (Mx ω ^ (r / 2))) :=
    ENNReal.measurable_ofReal.comp (hMm.pow_const _)
  have hAm' : Measurable (fun ω => ENNReal.ofReal (A ω ^ (r / 2))) :=
    ENNReal.measurable_ofReal.comp (hAm.pow_const _)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hMm'.aemeasurable hAm'.aemeasurable
  have hsq : ∀ x : Ω → ℝ, (∀ ω, 0 ≤ x ω) →
      ∫⁻ ω, (ENNReal.ofReal (x ω ^ (r / 2))) ^ (2 : ℝ) ∂μ = ∫⁻ ω, ENNReal.ofReal (x ω ^ r) ∂μ := by
    intro x hx
    refine lintegral_congr (fun ω => ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hx ω) _) (by norm_num),
      ← Real.rpow_mul (hx ω)]
    congr 2; ring
  set Bm : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (Mx ω ^ r) ∂μ with hBm
  set Aint : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (A ω ^ r) ∂μ with hAint
  have hI2 : ∫⁻ ω, ENNReal.ofReal ((∑ i, Y i ω ^ 2) ^ (r / 2)) ∂μ ≤ Bm ^ (1 / 2 : ℝ) * Aint ^ (1 / 2 : ℝ) := by
    calc ∫⁻ ω, ENNReal.ofReal ((∑ i, Y i ω ^ 2) ^ (r / 2)) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (Mx ω ^ (r / 2)) * ENNReal.ofReal (A ω ^ (r / 2)) ∂μ :=
          lintegral_mono hpt2
      _ ≤ _ := by
          have := hholder
          simp only [Pi.mul_apply] at this
          rw [hsq Mx hM0, hsq A hA0] at this
          exact this
  have hI2' : (∫⁻ ω, ENNReal.ofReal ((∑ i, Y i ω ^ 2) ^ (r / 2)) ∂μ) ^ (1 / r) ≤
      (Bm ^ (1 / r)) ^ (1 / 2 : ℝ) * (Aint ^ (1 / r)) ^ (1 / 2 : ℝ) := by
    calc (∫⁻ ω, ENNReal.ofReal ((∑ i, Y i ω ^ 2) ^ (r / 2)) ∂μ) ^ (1 / r)
        ≤ (Bm ^ (1 / 2 : ℝ) * Aint ^ (1 / 2 : ℝ)) ^ (1 / r) := ENNReal.rpow_le_rpow hI2 (by positivity)
      _ = (Bm ^ (1 / r)) ^ (1 / 2 : ℝ) * (Aint ^ (1 / r)) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm (1 / 2 : ℝ) (1 / r)]
  calc (∫⁻ ω, ENNReal.ofReal (A ω ^ r) ∂μ) ^ (1 / r)
      ≤ (∫⁻ ω, (ENNReal.ofReal |C ω| + ENNReal.ofReal μ0) ^ r ∂μ) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by positivity)
    _ ≤ (∫⁻ ω, (ENNReal.ofReal |C ω|) ^ r ∂μ) ^ (1 / r) + (∫⁻ _ : Ω, (ENNReal.ofReal μ0) ^ r ∂μ) ^ (1 / r) :=
        hmink
    _ = (∫⁻ ω, ENNReal.ofReal (|C ω| ^ r) ∂μ) ^ (1 / r) + ENNReal.ofReal μ0 := by rw [hF, hG]
    _ ≤ ENNReal.ofReal (khintchineConst r) * 2 *
          (∫⁻ ω, ENNReal.ofReal ((∑ i, Y i ω ^ 2) ^ (r / 2)) ∂μ) ^ (1 / r) + ENNReal.ofReal μ0 := by
        gcongr
    _ ≤ ENNReal.ofReal (khintchineConst r) * 2 *
          ((Bm ^ (1 / r)) ^ (1 / 2 : ℝ) * (Aint ^ (1 / r)) ^ (1 / 2 : ℝ)) + ENNReal.ofReal μ0 := by
        gcongr
    _ = _ := by rw [add_comm]

end SubdiffusiveProcess.Rosenthal
