import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Arithmetic

/-!
# The theta = 1/2 iteration

This is the discrete Grönwall part of the proof after the analytic one-step
estimate has been put in the displayed source shape.  The only exponent price
is the explicit factor `(1-alpha)⁻¹`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

/-- Uniform control of the dyadic scale energies from the printed contraction.
The numerical constant `8` is literal. -/
theorem dyadicSmallContrastIteration {A : ℕ → ℝ} {alpha B : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hA : ∀ n, 0 ≤ A n) (hB : 0 ≤ B)
    (hrec : ∀ n, A (n + 1) ≤ smallContrastContraction alpha * A n + B) :
    ∀ n, A n ≤ A 0 + 8 * (1 - alpha)⁻¹ * B := by
  have hq := smallContrastContraction_mem_Ioo halpha0 halpha1
  have hraw := affineContraction_uniform hq.1.le hq.2 hB (hA 0) hrec
  have hinv := inv_one_sub_smallContrastContraction_le halpha1
  intro n
  have hmul : B * (1 - smallContrastContraction alpha)⁻¹ ≤
      B * (8 * (1 - alpha)⁻¹) :=
    mul_le_mul_of_nonneg_left hinv hB
  have hn := hraw n
  rw [div_eq_mul_inv] at hn
  calc
    A n ≤ A 0 + B * (1 - smallContrastContraction alpha)⁻¹ := hn
    _ ≤ A 0 + 8 * (1 - alpha)⁻¹ * B := by
      rw [mul_assoc, mul_comm B]
      linarith

/-- The source's recurrence after the perturbative coefficient has been
absorbed by `smallContrastThreshold`. -/
theorem dyadicSmallContrastIteration_of_rawCoefficient
    {d : ℕ} {A : ℕ → ℝ} {alpha delta B : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hA : ∀ n, 0 ≤ A n) (hB : 0 ≤ B)
    (hrec : ∀ n,
      A (n + 1) ≤
        ((1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
          (1 / 2 : ℝ) ^ (1 - alpha)) * A n + B) :
    ∀ n, A n ≤ A 0 + 8 * (1 - alpha)⁻¹ * B := by
  have hcoef := dyadic_smallContrast_contraction halpha0 halpha1 hdelta
  apply dyadicSmallContrastIteration halpha0 halpha1 hA hB
  intro n
  have hAn := hA n
  exact (hrec n).trans <| by
    gcongr

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
