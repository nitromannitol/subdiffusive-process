module

public import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
public import SubdiffusiveProcess.Frozen.Section6.Defs.AnchoredCutoff

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open _root_.SubdiffusiveProcess.Model Homogenization

noncomputable section

variable {d : ℕ}

theorem anchoredCutoff_eq_exp (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (x : Vec d) :
    anchoredCutoff M L omega x = Real.exp (anchoredPartialSum omega L x) := by
  rw [anchoredCutoff, aCutoff, aCutoff, ← Real.exp_sub, anchoredPartialSum]
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The coordinate gradient as a linear map -/

/-- The coordinate readout of a continuous linear functional. -/
def gradOfCLM (T : Vec d →L[ℝ] ℝ) : Vec d :=
  fun i => T (Pi.single i 1)

@[simp]
theorem shellGradient_eq_gradOfCLM (g : PotentialField d) (x : Vec d) :
    shellGradient g x = gradOfCLM (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x) :=
  rfl

@[simp]
theorem gradOfCLM_sub (T S : Vec d →L[ℝ] ℝ) :
    gradOfCLM (T - S) = gradOfCLM T - gradOfCLM S :=
  rfl

@[simp]
theorem gradOfCLM_smul (c : ℝ) (T : Vec d →L[ℝ] ℝ) :
    gradOfCLM (c • T) = c • gradOfCLM T :=
  rfl

theorem norm_gradOfCLM_le (T : Vec d →L[ℝ] ℝ) : ‖gradOfCLM T‖ ≤ ‖T‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg T)).2 fun i => ?_
  have hsingle : ‖(Pi.single i (1 : ℝ) : Vec d)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hij : j = i
    · subst hij
      simp
    · simp [hij]
  calc ‖T (Pi.single i 1)‖ ≤ ‖T‖ * ‖(Pi.single i (1 : ℝ) : Vec d)‖ :=
        T.le_opNorm _
    _ ≤ ‖T‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hsingle (norm_nonneg T)
    _ = ‖T‖ := mul_one _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
