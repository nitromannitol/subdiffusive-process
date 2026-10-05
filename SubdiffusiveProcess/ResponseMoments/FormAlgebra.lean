module

public import SubdiffusiveProcess.ResponseMoments.Forms
public import Mathlib.Tactic

@[expose] public section

/-!
# Bilinearity of a candidate energy measure

The right-hand versions of the two linearity fields of
`SubdiffusiveProcess.ResponseMoments.LocalEnergy`, used throughout Subsection `mfd:sec-compare`
(`mfd:sec-compare`).
-/

open MeasureTheory Set

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments
namespace LocalEnergy

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {X : Type*} [MeasurableSpace X]

theorem gam_add_right (E : LocalEnergy V X) (u v w : V) (s : Set X) :
    E.gam u (v + w) s = E.gam u v s + E.gam u w s := by
  rw [gam_symm E u (v + w) s, gam_symm E u v s, gam_symm E u w s,
    gam_add_left E v w u s]

theorem gam_smul_right (E : LocalEnergy V X) (c : ℝ) (u v : V) (s : Set X) :
    E.gam u (c • v) s = c * E.gam u v s := by
  rw [E.gam_symm u (c • v) s, E.gam_smul_left c v u s, E.gam_symm v u s]

theorem gam_zero_left (E : LocalEnergy V X) (v : V) (s : Set X) :
    E.gam 0 v s = 0 := by
  have h := E.gam_smul_left (0 : ℝ) (0 : V) v s
  simpa using h

theorem gam_sub_left (E : LocalEnergy V X) (u v w : V) (s : Set X) :
    E.gam (u - v) w s = E.gam u w s - E.gam v w s := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ v]
  rw [E.gam_add_left, E.gam_smul_left]
  ring

end LocalEnergy
end ResponseMoments
end SubdiffusiveProcess
