module

public import SubdiffusiveProcess.BoundedMultiplier.RestrictedEvent
public import Mathlib.Data.ENNReal.Real

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.BoundedMultiplier

/-- A conditional real oscillation on a nonempty subset is bounded by the
extended-valued oscillation of the full set. -/
theorem ofReal_oscillationOn_le {d : ℕ} {S B : Set (Vec d)} (hS : S.Nonempty)
    (hSB : S ⊆ B) (f : Vec d → ℝ) :
    ENNReal.ofReal (oscillationOn S f) ≤
      ⨆ x ∈ B, ⨆ y ∈ B, ENNReal.ofReal |f x - f y| := by
  let R : ℝ≥0∞ := ⨆ x ∈ B, ⨆ y ∈ B, ENNReal.ofReal |f x - f y|
  by_cases hR : R = ⊤
  · change ENNReal.ofReal (oscillationOn S f) ≤ R
    rw [hR]
    exact le_top
  · apply (ENNReal.ofReal_le_iff_le_toReal hR).mpr
    apply csSup_le
    · obtain ⟨x, hx⟩ := hS
      exact ⟨0, x, hx, x, hx, by simp only [sub_self, abs_zero]⟩
    · rintro r ⟨x, hx, y, hy, rfl⟩
      have hxy : ENNReal.ofReal |f x - f y| ≤ R :=
        le_iSup_of_le x (le_iSup_of_le (hSB hx)
          (le_iSup_of_le y (le_iSup_of_le (hSB hy) le_rfl)))
      exact (ENNReal.ofReal_le_iff_le_toReal hR).mp hxy

/-- The compact three-eighths comparison window is contained in the parent cube. -/
theorem comparison_window_subset {d : ℕ} (m : ℤ) (z : Vec d) :
    {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} ⊆ translatedCube d m z := by
  have heq : {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} =
      Metric.closedBall z (3 * (3 : ℝ) ^ m / 8) := by
    ext x
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm]
  rw [heq, translatedCube_eq_metricBall]
  apply Metric.closedBall_subset_ball
  have hpow : 0 < (3 : ℝ) ^ m := by positivity
  linarith

/-- Convert the interior-window oscillation estimate to the paper's
extended-valued parent oscillation. -/
theorem ofReal_oscillation_estimate {d : ℕ} (m : ℤ) (z : Vec d)
    (B' : Set (Vec d)) (f : Vec d → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hest : oscillationOn B' f ≤ K *
      oscillationOn {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} f) :
    ENNReal.ofReal (oscillationOn B' f) ≤ ENNReal.ofReal K *
      ⨆ x ∈ translatedCube d m z, ⨆ y ∈ translatedCube d m z,
        ENNReal.ofReal |f x - f y| := by
  have hnonempty : {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8}.Nonempty :=
    ⟨z, by simp only [Set.mem_setOf_eq, sub_self, norm_zero]; positivity⟩
  calc
    ENNReal.ofReal (oscillationOn B' f) ≤ ENNReal.ofReal (K *
      oscillationOn {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} f) :=
        ENNReal.ofReal_le_ofReal hest
    _ = ENNReal.ofReal K * ENNReal.ofReal
      (oscillationOn {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} f) :=
        ENNReal.ofReal_mul hK
    _ ≤ _ := mul_le_mul_right (ofReal_oscillationOn_le hnonempty
      (comparison_window_subset m z) f) _

end SubdiffusiveProcess.BoundedMultiplier
