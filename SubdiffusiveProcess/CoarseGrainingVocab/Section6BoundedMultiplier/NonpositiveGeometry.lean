module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveRadius
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitGeometry

@[expose] public section

/-!
# Geometry for the direct nonpositive-scale branch
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- The deterministic outer localization ball stays inside the frozen
three-eighths oscillation window. -/
theorem euclideanBall_nonpositiveRadius_subset_oscillationWindow
    {m : ℤ} {z x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4) :
    euclideanBall x
        (boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m) ⊆
      {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} := by
  intro y hy
  have hR : 0 < boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m :=
    mul_pos (boundedMultiplierNonpositiveRadiusFloor_pos d) (by positivity)
  have hyx : ‖y - x‖ <
      boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m :=
    euclideanBall_subset_metricBall hR hy
  have htri : ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := by
    calc
      ‖y - z‖ = ‖(y - x) + (x - z)‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
  have hfloor := boundedMultiplierNonpositiveRadiusFloor_le_eighth d
  have hpow : 0 ≤ (3 : ℝ) ^ m := by positivity
  have hRle : boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m ≤
      (3 : ℝ) ^ m / 8 := by
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hfloor hpow
  change ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8
  apply le_of_lt
  calc
    ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := htri
    _ < boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m +
        (3 : ℝ) ^ m / 4 := by linarith
    _ ≤ (3 : ℝ) ^ m / 8 + (3 : ℝ) ^ m / 4 :=
      add_le_add hRle le_rfl
    _ = 3 * (3 : ℝ) ^ m / 8 := by ring

/-- Failure of the first deterministic sub-unit ball can occur only at a
dimension-only bounded target depth. -/
theorem three_pow_depth_lt_of_nonpositiveFirstSubunitBall_lt
    [NeZero d] {m : ℤ} {R : ℝ}
    (hR : boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m ≤ R)
    {j : ℕ}
    (hshallow : R / (12 * (d : ℝ)) <
      1 / 2 * (3 : ℝ) ^ (m - (j : ℤ))) :
    (3 : ℝ) ^ j <
      6 * (d : ℝ) / boundedMultiplierNonpositiveRadiusFloor d := by
  have hdNat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hfloor := boundedMultiplierNonpositiveRadiusFloor_pos d
  have hA : 0 < (3 : ℝ) ^ m := by positivity
  have hP : 0 < (3 : ℝ) ^ j := by positivity
  have hden : 0 < 12 * (d : ℝ) := mul_pos (by norm_num) hd
  have hlower : boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m /
        (12 * (d : ℝ)) ≤ R / (12 * (d : ℝ)) :=
    div_le_div_of_nonneg_right hR hden.le
  have hstrict : boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m /
        (12 * (d : ℝ)) <
      1 / 2 * (3 : ℝ) ^ (m - (j : ℤ)) := hlower.trans_lt hshallow
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast] at hstrict
  have hscaled : boundedMultiplierNonpositiveRadiusFloor d <
      6 * (d : ℝ) / (3 : ℝ) ^ j := by
    have hscalePos : 0 < (12 * (d : ℝ)) / (3 : ℝ) ^ m :=
      div_pos (mul_pos (by norm_num) hd) hA
    have hmul := mul_lt_mul_of_pos_right hstrict hscalePos
    convert hmul using 1 <;>
      (field_simp [hd.ne', hA.ne', hP.ne'] <;> ring)
  have hcross : boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ j <
      6 * (d : ℝ) := (lt_div_iff₀ hP).1 hscaled
  exact (lt_div_iff₀ hfloor).2 (by simpa only [mul_comm] using hcross)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
