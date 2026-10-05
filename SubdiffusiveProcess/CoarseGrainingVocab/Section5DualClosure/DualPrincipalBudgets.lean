module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteMajorantAssembly

@[expose] public section




open MeasureTheory

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

/-- `delta ^ 4 * h ^ 2 ≤ 1` in the one-step scaling regime. -/
theorem delta_four_mul_sq_le_one {delta h : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hh : 0 ≤ h) (hscale : delta * h ≤ 1) :
    delta ^ 4 * h ^ 2 ≤ 1 := by
  have hstep : delta ^ 2 * h ≤ 1 := by nlinarith
  have hstep0 : 0 ≤ delta ^ 2 * h := by positivity
  nlinarith

/-- `2 * tau * h / d ≤ 2` in the one-step scaling regime. -/
theorem two_tau_mul_div_le_two {delta tau h d : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (_htau0 : 0 ≤ tau) (htau : tau ≤ delta ^ 2)
    (hh : 0 ≤ h) (hd : 1 ≤ d) (hscale : delta * h ≤ 1) :
    2 * tau * h / d ≤ 2 := by
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd
  have hnum : tau * h ≤ 1 := by nlinarith
  rw [div_le_iff₀ hd0]
  nlinarith

/-- **The dual principal budgets.**  Sign-flipped counterpart of the primal
`primal_principal_budgets_of_weight`, delivering both hypotheses that
`one_step_lower_penultimate_of_ae_finite_majorants` consumes. -/
theorem dual_principal_budgets_of_weight
    {delta tau h d C B cellStarInv previousInv weight principal : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (htau0 : 0 ≤ tau) (htau : tau ≤ delta ^ 2)
    (hh : 0 ≤ h) (hd : 1 ≤ d)
    (hscale : delta * h ≤ 1) (hC : 0 < C) (hB : 0 ≤ B)
    (hcell0 : 0 ≤ cellStarInv) (hprevious0 : 0 ≤ previousInv)
    (hy : delta ^ 2 * |Real.log delta| ≤ 1)
    (hcell : cellStarInv ≤
      (1 + B * (delta ^ 2 * |Real.log delta|)) * previousInv)
    (hprincipal : principal = cellStarInv * weight)
    (hweight : weight ≤
      1 + 2 * tau * h / d + C * delta ^ 4 * h ^ 2 + C * delta ^ 17) :
    principal ≤ ((3 + 2 * C) * (1 + B)) * previousInv ∧
      principal ≤
        (1 + 2 * tau * h / d + (C * (1 + B)) * delta ^ 4 * h ^ 2) *
            cellStarInv +
          (C * (1 + B)) * delta ^ 15 * previousInv := by
  have hy0 : 0 ≤ delta ^ 2 * |Real.log delta| := by positivity
  have hcellB : cellStarInv ≤ (1 + B) * previousInv := by
    refine hcell.trans ?_
    have hBy : B * (delta ^ 2 * |Real.log delta|) ≤ B := by
      simpa using mul_le_mul_of_nonneg_left hy hB
    exact mul_le_mul_of_nonneg_right (by linarith) hprevious0
  have hfour : delta ^ 4 * h ^ 2 ≤ 1 :=
    delta_four_mul_sq_le_one hdelta0 hdelta1 hh hscale
  have hfour0 : 0 ≤ delta ^ 4 * h ^ 2 := by positivity
  have htwo : 2 * tau * h / d ≤ 2 :=
    two_tau_mul_div_le_two hdelta0 hdelta1 htau0 htau hh hd hscale
  have htwo0 : 0 ≤ 2 * tau * h / d := by
    have hd0 : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd
    positivity
  have hd17 : delta ^ 17 ≤ 1 := pow_le_one₀ hdelta0 hdelta1
  have hd170 : (0 : ℝ) ≤ delta ^ 17 := by positivity
  have hd17le15 : delta ^ 17 ≤ delta ^ 15 :=
    pow_le_pow_of_le_one hdelta0 hdelta1 (by norm_num)
  refine ⟨?_, ?_⟩
  · -- rough bound
    have hweightBound : weight ≤ 3 + 2 * C := by nlinarith
    calc
      principal = cellStarInv * weight := hprincipal
      _ ≤ cellStarInv * (3 + 2 * C) :=
        mul_le_mul_of_nonneg_left hweightBound hcell0
      _ ≤ ((1 + B) * previousInv) * (3 + 2 * C) := by
        exact mul_le_mul_of_nonneg_right hcellB (by linarith)
      _ = ((3 + 2 * C) * (1 + B)) * previousInv := by ring
  · -- sharp bound
    have hsplit :
        cellStarInv * weight ≤
          cellStarInv * (1 + 2 * tau * h / d + C * delta ^ 4 * h ^ 2) +
            cellStarInv * (C * delta ^ 17) := by
      have := mul_le_mul_of_nonneg_left hweight hcell0
      nlinarith
    have htail : cellStarInv * (C * delta ^ 17) ≤
        (C * (1 + B)) * delta ^ 15 * previousInv := by
      have hstep1 : cellStarInv * (C * delta ^ 17) ≤
          ((1 + B) * previousInv) * (C * delta ^ 17) :=
        mul_le_mul_of_nonneg_right hcellB (by positivity)
      have hstep2 : ((1 + B) * previousInv) * (C * delta ^ 17) ≤
          ((1 + B) * previousInv) * (C * delta ^ 15) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hd17le15 hC.le
      calc
        cellStarInv * (C * delta ^ 17) ≤
            ((1 + B) * previousInv) * (C * delta ^ 17) := hstep1
        _ ≤ ((1 + B) * previousInv) * (C * delta ^ 15) := hstep2
        _ = (C * (1 + B)) * delta ^ 15 * previousInv := by ring
    have hhead :
        cellStarInv * (1 + 2 * tau * h / d + C * delta ^ 4 * h ^ 2) ≤
          (1 + 2 * tau * h / d + (C * (1 + B)) * delta ^ 4 * h ^ 2) *
            cellStarInv := by
      have hCA : C ≤ C * (1 + B) := by nlinarith
      have hterm : C * delta ^ 4 * h ^ 2 ≤
          (C * (1 + B)) * delta ^ 4 * h ^ 2 := by
        have := mul_le_mul_of_nonneg_right hCA hfour0
        nlinarith
      nlinarith
    calc
      principal = cellStarInv * weight := hprincipal
      _ ≤ cellStarInv * (1 + 2 * tau * h / d + C * delta ^ 4 * h ^ 2) +
            cellStarInv * (C * delta ^ 17) := hsplit
      _ ≤ (1 + 2 * tau * h / d + (C * (1 + B)) * delta ^ 4 * h ^ 2) *
              cellStarInv +
            (C * (1 + B)) * delta ^ 15 * previousInv :=
        add_le_add hhead htail

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
