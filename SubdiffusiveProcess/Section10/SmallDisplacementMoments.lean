import SubdiffusiveProcess.Section10.SmallDisplacementNegative

open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.SmallDisplacement
open EndpointPaths

/-- The literal Euclidean maximum has no zero atom at any source time 0<t≤1. -/
theorem maximum_zero_null_of_exit_moments {d : ℕ} (P : Measure (DiffusionPath d))
    [IsProbabilityMeasure P] (Cp p eta : ℝ) (hp : 0 < p) (heta : 0 < eta)
    (hmoment : ∀ k : ℕ, (∫⁻ w, smallExit k w ^ p ∂P) ≤
      ENNReal.ofReal (Cp * (3 : ℝ) ^ (-(p * (2 + eta) * k))))
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1) : P {w | maximum t w = 0} = 0 :=
  zero_null_of_small_ball P (maximum t) (displacementConstant Cp p eta * (t : ℝ) ^ (-p))
    (p * (2 + eta)) (mul_pos hp (by linarith))
    (fun epsilon heps heps1 => small_displacement_of_exit_moments P Cp p eta hp heta hmoment
      t ht ht1 epsilon heps heps1)

/-- Negative maximal moments in the strict source range, with the exact time
normalization. Zero values use ENNReal powers and are proved null. -/
theorem maximal_negative_moment_of_exit_moments {d : ℕ} (P : Measure (DiffusionPath d))
    [IsProbabilityMeasure P] (Cp p eta : ℝ) (hp : 0 < p) (heta : 0 < eta)
    (hmoment : ∀ k : ℕ, (∫⁻ w, smallExit k w ^ p ∂P) ≤
      ENNReal.ofReal (Cp * (3 : ℝ) ^ (-(p * (2 + eta) * k))))
    (q : ℝ) (hq : 0 < q) (hqA : q < p * (2 + eta))
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1) :
    (∫⁻ w, ENNReal.ofReal (maximum t w) ^ (-q) ∂P) ≤
      ENNReal.ofReal (negativeMomentConstant (displacementConstant Cp p eta) (p * (2 + eta)) q *
        (t : ℝ) ^ (-q / (2 + eta))) := by
  let S : ℝ := (t : ℝ) ^ (1 / (2 + eta))
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have hS : 0 < S := Real.rpow_pos_of_pos ht0 _
  let Y : DiffusionPath d → ℝ := fun w => maximum t w / S
  have hY : Measurable Y := (maximum_measurable t).div_const S
  have hY0 : ∀ w, 0 ≤ Y w := fun w => div_nonneg (maximum_nonneg w t) hS.le
  have hsmall : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      P {w | Y w ≤ epsilon} ≤
        ENNReal.ofReal (displacementConstant Cp p eta * epsilon ^ (p * (2 + eta))) := by
    intro epsilon heps heps1
    have heq : {w | Y w ≤ epsilon} = {w | maximum t w ≤ epsilon * S} := by
      ext w
      exact div_le_iff₀ hS
    rw [heq]
    exact scaled_small_displacement P Cp p eta hp heta hmoment t ht ht1 epsilon heps heps1
  have hneg := negative_moment_of_small_ball P Y hY hY0
    (displacementConstant Cp p eta) (p * (2 + eta)) q (displacementConstant_pos Cp p eta).le
    (mul_pos hp (by linarith)) hq hqA hsmall
  have hSfactor : S ^ (-q) = (t : ℝ) ^ (-q / (2 + eta)) := by
    dsimp only [S]
    rw [← Real.rpow_mul (x := (t : ℝ)) t.property (1 / (2 + eta)) (-q)]
    congr 1
    ring
  have hfactor : ∀ w, ENNReal.ofReal (maximum t w) ^ (-q) =
      ENNReal.ofReal ((t : ℝ) ^ (-q / (2 + eta))) * ENNReal.ofReal (Y w) ^ (-q) := by
    intro w
    have hmax : maximum t w = S * Y w := by dsimp [Y]; field_simp [hS.ne']
    rw [hmax, ENNReal.ofReal_mul hS.le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (-q),
      ENNReal.ofReal_rpow_of_pos hS, hSfactor]
  calc (∫⁻ w, ENNReal.ofReal (maximum t w) ^ (-q) ∂P) =
      ENNReal.ofReal ((t : ℝ) ^ (-q / (2 + eta))) *
        ∫⁻ w, ENNReal.ofReal (Y w) ^ (-q) ∂P := by
          simp_rw [hfactor]
          exact lintegral_const_mul _ ((ENNReal.continuous_rpow_const (y := -q)).measurable.comp hY.ennreal_ofReal)
    _ ≤ ENNReal.ofReal ((t : ℝ) ^ (-q / (2 + eta))) *
      ENNReal.ofReal (negativeMomentConstant (displacementConstant Cp p eta) (p * (2 + eta)) q) :=
        mul_le_mul_right hneg _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (p := (t : ℝ) ^ (-q / (2 + eta)))
        (Real.rpow_nonneg t.property (-q / (2 + eta))), mul_comm]

end SubdiffusiveProcess.Section10.SmallDisplacement
