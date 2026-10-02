import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Variational.DualEnergy

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Analysis

/-- The actual quadratic dual energy controls its volume Hilbert norm. -/
theorem limitEnergy_norm_sq_le {d : ℕ} (Q : TopologicalSpace.Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q)
    (hu : (limitFormEnergy G u).toENNReal ≠ ∞) :
    ‖u‖ ^ 2 ≤ ‖G‖ * (limitFormEnergy G u).toReal := by
  have ht : limitFormEnergy G u ≠ (⊤ : EReal) := EReal.toENNReal_ne_top_iff.mp hu
  have hb : limitFormEnergy G u ≠ (⊥ : EReal) :=
    ne_of_gt (lt_of_lt_of_le (by simp : (⊥ : EReal) < 0) (limitFormEnergy_nonneg G u))
  exact norm_sq_le_operatorNorm_mul_quadraticDual G u (limitFormEnergy G u).toReal
    (EReal.coe_toReal ht hb).symm

theorem limitEnergy_coercive {d : ℕ} (Q : TopologicalSpace.Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : DomainL2 Q,
      ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal C * (limitFormEnergy G u).toENNReal := by
  refine ⟨‖G‖ + 1, by positivity, fun u => ?_⟩
  by_cases hu : (limitFormEnergy G u).toENNReal = ∞
  · rw [hu, ENNReal.mul_top (by positivity)]
    exact le_top
  · have he : 0 ≤ (limitFormEnergy G u).toReal :=
      EReal.toReal_nonneg (limitFormEnergy_nonneg G u)
    have h := (limitEnergy_norm_sq_le Q G u hu).trans
      (mul_le_mul_of_nonneg_right (by linarith : ‖G‖ ≤ ‖G‖ + 1) he)
    have ht : limitFormEnergy G u ≠ (⊤ : EReal) := EReal.toENNReal_ne_top_iff.mp hu
    have hb : limitFormEnergy G u ≠ (⊥ : EReal) :=
      ne_of_gt (lt_of_lt_of_le (by simp : (⊥ : EReal) < 0) (limitFormEnergy_nonneg G u))
    rw [← EReal.coe_toReal ht hb, EReal.real_coe_toENNReal, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h

/-- Masking a null exceptional inverse by zero leaves only the zero finite-energy class. -/
theorem eq_zero_of_zero_limitEnergy_finite {d : ℕ}
    (Q : TopologicalSpace.Opens (SpatialCoordinates d)) (u : DomainL2 Q)
    (hu : (limitFormEnergy (0 : DomainL2 Q →L[ℝ] DomainL2 Q) u).toENNReal ≠ ∞) :
    u = 0 := by
  have h := limitEnergy_norm_sq_le Q 0 u hu
  rw [norm_zero, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])

end SubdiffusiveProcess.Analysis
