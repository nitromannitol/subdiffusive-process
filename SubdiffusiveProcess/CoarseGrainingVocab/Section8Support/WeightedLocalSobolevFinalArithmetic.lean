module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMassCore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMeasure
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
theorem weightedSobolev_scale_half_sq {d : ℕ} (Q : TriadicCube d) :
    (cubeBesovScaleWeight (-1/2) Q)^2 = cubeScaleFactor Q := by
  rw [pow_two, cubeBesovScaleWeight_mul_eq_scaleWeight_add]
  norm_num only [show (-1 / 2 : ℝ) + (-1 / 2) = -1 by norm_num]
  exact cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor Q

theorem weightedSobolev_ofReal_order_ge_one {p : ℝ} (hp : 2 < p) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
  simpa using ENNReal.ofReal_le_ofReal (show (1:ℝ) ≤ p by linarith)

theorem weightedSobolev_final_constant_pos {Cp Ce p : ℝ} (hCp : 0 < Cp) (hCe : 0 < Ce) :
    0 < (2 * (Cp * (8:ℝ)^(1/p) * Ce + Ce))^2 := by
  have h8 : 0 < (8:ℝ)^(1/p) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

theorem weightedSobolev_energy_factor {C M p L S E : ℝ} :
    C * (1+M)^(2/p) * S^2 * (L⁻¹ * E) =
    C * (1+M)^(2/p) * S^2 * L⁻¹ * E := by ring

theorem weightedSobolev_norm_square_bound {x : ℝ≥0∞} {A B : ℝ}
    (hA : 0 ≤ A) (h : x ≤ ENNReal.ofReal A) (hB : A^2 ≤ B) :
    x^2 ≤ ENNReal.ofReal B := by
  calc
    x^2 ≤ (ENNReal.ofReal A)^2 := pow_le_pow_left' h 2
    _ = ENNReal.ofReal (A^2) := (ENNReal.ofReal_pow hA 2).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hB

theorem weightedSobolev_origin_scale (d : ℕ) (m : ℤ) :
    cubeScaleFactor (originCube d m) = (3:ℝ)^m := by
  simp [cubeScaleFactor, originCube]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
