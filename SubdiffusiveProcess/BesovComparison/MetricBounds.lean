import SubdiffusiveProcess.BesovComparison.MetricComparison

/-! Uniform dimension-only norm comparison for the two distance conventions. -/
open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.BesovComparison
variable {d : ℕ}

def metricConstant (d : ℕ) : ℝ≥0∞ := ((d : ℝ≥0∞) + 1) ^ (d + 1)

theorem one_le_metricConstant (d : ℕ) : 1 ≤ metricConstant d := by
  apply one_le_pow₀
  exact le_add_self

theorem metricConstant_ne_top (d : ℕ) : metricConstant d ≠ ∞ := by
  unfold metricConstant
  finiteness

theorem metric_power_bound [NeZero d] (s p : ℝ) (hs : 0 < s) (hs1 : s < 1) (hp : 1 ≤ p) :
    ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + s*p)) ≤ metricConstant d ^ p := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have ha : 0 ≤ (d : ℝ) + s*p := by positivity
  have he : (d : ℝ) + s*p ≤ ((d : ℝ)+1)*p := by
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  rw [← ENNReal.ofReal_rpow_of_pos hd]
  unfold metricConstant
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have hb : ENNReal.ofReal (d : ℝ) ≤ (d : ℝ≥0∞) + 1 := by simp
  have hex : (d : ℝ) + s*p ≤ (d+1 : ℕ)*p := by exact_mod_cast he
  exact (ENNReal.rpow_le_rpow hb ha).trans
    (ENNReal.rpow_le_rpow_of_exponent_le (by exact le_add_self) hex)

theorem wsp_le_ambient (m : ℤ) (s p : ℝ) (hs : 0 < s) (hp : 0 < p) (u : Vec d → ℝ) :
    wsp d m s p u ≤ ambientWsp d m s p u := by
  unfold wsp ambientWsp
  rw [one_div]
  apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hp.le)
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro x
  apply lintegral_mono
  intro y
  exact scalarEnergy_euclidean_le _ p (by positivity) u x y

theorem ambient_le_metric_mul_wsp [NeZero d] (m : ℤ) (s p : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hp : 1 ≤ p) (u : Vec d → ℝ) :
    ambientWsp d m s p u ≤ metricConstant d * wsp d m s p u := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have ha : 0 < (d : ℝ) + s*p := by positivity
  have hK : metricConstant d ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp0.le (metricConstant_ne_top d)
  have hpoint : ∀ x y : Vec d,
      scalarEnergy ((d : ℝ)+s*p) p u (dist x y) x y ≤
        metricConstant d ^ p * scalarEnergy ((d : ℝ)+s*p) p u (euclideanDist x y) x y := by
    intro x y
    exact (scalarEnergy_ambient_le _ p ha hp0 u x y).trans
      (mul_le_mul' (metric_power_bound s p hs hs1 hp) le_rfl)
  have hint : (∫⁻ x in cube d m, ∫⁻ y in cube d m,
      scalarEnergy ((d : ℝ)+s*p) p u (dist x y) x y) ≤
      metricConstant d ^ p * ∫⁻ x in cube d m, ∫⁻ y in cube d m,
        scalarEnergy ((d : ℝ)+s*p) p u (euclideanDist x y) x y := by
    calc
      _ ≤ ∫⁻ x in cube d m, ∫⁻ y in cube d m,
          metricConstant d ^ p * scalarEnergy ((d : ℝ)+s*p) p u (euclideanDist x y) x y :=
        lintegral_mono fun x => lintegral_mono fun y => hpoint x y
      _ = _ := by simp_rw [lintegral_const_mul' _ _ hK]
  unfold ambientWsp wsp
  rw [one_div]
  calc
    _ ≤ (ENNReal.ofReal s * (volume (cube d m))⁻¹ *
        (metricConstant d ^ p * ∫⁻ x in cube d m, ∫⁻ y in cube d m,
          scalarEnergy ((d : ℝ)+s*p) p u (euclideanDist x y) x y)) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hint) (inv_nonneg.mpr hp0.le)
    _ = _ := by
      rw [mul_left_comm (ENNReal.ofReal s * _),
        ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le),
        ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]
      rfl

end SubdiffusiveProcess.BesovComparison
