module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_ahom_ratio
public import Mathlib.Tactic

@[expose] public section

open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- A small-disorder threshold absorbs the deterministic all-cutoff
`ahom` ratio loss into any prescribed triadic exponential rate. -/
theorem lem_as_coarse_shallow_grid_tau_absorption
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        M.delta ≤ delta0 → ∀ k : ℕ,
          Real.exp (4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) ≤
            (3 : ℝ) ^ (rho * (k : ℝ)) := by
  set D := 1 + 2 * Real.log 2 with hD
  set T := rho * Real.log 3 with hT
  set delta0 := min 1 (T / D) with hdelta0
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hTpos : 0 < T := mul_pos hrho hlog3pos
  have hDpos : 0 < D := by nlinarith
  have hdelta0_pos : 0 < delta0 := by
    rw [hdelta0]
    exact lt_min_iff.mpr ⟨by norm_num, div_pos hTpos hDpos⟩
  have hdelta0_le_one : delta0 ≤ 1 := by
    rw [hdelta0]
    exact min_le_left _ _
  have hdelta0_le_TdivD : delta0 ≤ T / D := by
    rw [hdelta0]
    exact min_le_right _ _
  have h_two_log2_le_D : 2 * Real.log 2 ≤ D := by nlinarith
  have hineq : 2 * Real.log 2 * (T / D) ≤ T := by
    calc
      2 * Real.log 2 * (T / D) = (2 * Real.log 2 / D) * T := by ring
      _ ≤ 1 * T := by
        nlinarith [(div_le_one hDpos).mpr h_two_log2_le_D]
      _ = T := by ring
  refine ⟨delta0, hdelta0_pos, hdelta0_le_one, ?_⟩
  intro d M hMdelta k
  have hdelta_pos : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta_le_half : M.delta ≤ 1/2 := M.shellPrefix.delta_le_half
  have htauSq_le : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (Real.log 2 / 2) * M.delta ^ 2 :=
    SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
  have hdelta_sq_le_delta0 : M.delta ^ 2 ≤ delta0 := by
    have h1 : M.delta ^ 2 ≤ delta0 ^ 2 := by
      nlinarith
    have h2 : delta0 ^ 2 ≤ delta0 := by
      nlinarith
    nlinarith
  have htauSq_bound : 4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ T := by
    have h1 : 4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 4 * ((Real.log 2 / 2) * M.delta ^ 2) := by
      nlinarith
    have h2 : 4 * ((Real.log 2 / 2) * M.delta ^ 2) = 2 * Real.log 2 * M.delta ^ 2 := by ring
    have h3 : 2 * Real.log 2 * M.delta ^ 2 ≤ 2 * Real.log 2 * delta0 := by
      nlinarith
    have h4 : 2 * Real.log 2 * delta0 ≤ T := by
      nlinarith
    nlinarith
  have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have h_exp_arg : 4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ) ≤ T * (k : ℝ) := by
    nlinarith
  calc
    Real.exp (4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) ≤
        Real.exp (T * (k : ℝ)) := Real.exp_le_exp.mpr h_exp_arg
    _ = Real.exp (Real.log (3 : ℝ) * (rho * (k : ℝ))) := by
      rw [hT]
      ring
    _ = (3 : ℝ) ^ (rho * (k : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) (rho * (k : ℝ))]

end Paper

