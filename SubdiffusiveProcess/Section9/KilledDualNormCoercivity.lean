module

public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Variational.DualEnergy

@[expose] public section

open MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section9

/-- The norm of the ACTUAL inverse controls the real dual energy on its literal
finite-energy domain. No separate mass or coercivity promise is needed. -/
theorem killed_dual_norm_coercivity {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q)
    (hu : (limitFormEnergy G u).toENNReal ≠ ⊤) :
    ‖u‖ ^ 2 ≤ max 1 ‖G‖ * (limitFormEnergy G u).toENNReal.toReal := by
  have htop : limitFormEnergy G u ≠ (⊤ : EReal) := EReal.toENNReal_ne_top_iff.mp hu
  have hbot : limitFormEnergy G u ≠ (⊥ : EReal) :=
    ne_bot_of_le_ne_bot (by simp) (limitFormEnergy_nonneg G u)
  have he : limitFormEnergy G u = ((limitFormEnergy G u).toReal : EReal) :=
    (EReal.coe_toReal htop hbot).symm
  have hb := norm_sq_le_operatorNorm_mul_quadraticDual G u (limitFormEnergy G u).toReal he
  rw [← EReal.toReal_toENNReal (limitFormEnergy_nonneg G u)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg)

end SubdiffusiveProcess.Section9
