module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CampanatoRebaseArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ParameterAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.TopWindow

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The dimension-only volume ratio at the maximal admissible top depth. -/
def topWindowRatio (d : ℕ) : ℝ := (3 : ℝ) ^ (5 : ℕ) * Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d)

theorem topWindowRatio_nonneg (d : ℕ) : 0 ≤ topWindowRatio d := by
  unfold topWindowRatio
  positivity

/-- The constant produced by the row-1 passage. -/
def rowOneConst (d : ℕ) (Cabs Kforce exponential : ℝ) : ℝ :=
  Cabs * max (topWindowRatio d) (5 / 2 * Kforce * exponential)

/-- **The row-1 passage, on abstract reals.**  The full-domain estimate at top
depth `m - 5`, the top-window transfer and the exponential absorption combine
into the row-1 shape. -/
theorem interiorRowOne_arith {d : ℕ}
    {alpha ell n m Aexp Cabs Kforce exponential oscEll oscTop global data : ℝ}
    (halpha : alpha ≤ 1) (hellm : ell ≤ m)
    (hglobal : 0 ≤ global) (hdata : 0 ≤ data)
    (hAexp : 0 ≤ Aexp) (hKforce : 0 ≤ Kforce) (hexponential : 0 ≤ exponential)
    (hCabs : 0 ≤ Cabs)
    (habs : Aexp ≤ Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4))
    (htop : oscTop ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hfull : (3 : ℝ) ^ (-ell) * oscEll ≤
      Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
        5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
          ((3 : ℝ) ^ (m / 2) * data))) :
    (3 : ℝ) ^ (alpha * (n - ell)) * oscEll ≤
      rowOneConst d Cabs Kforce exponential * (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  set M0 : ℝ := max (topWindowRatio d) (5 / 2 * Kforce * exponential) with hM0
  have hM0nonneg : 0 ≤ M0 :=
    le_trans (topWindowRatio_nonneg d) (le_max_left _ _)
  -- the top-window leg
  have hlegTop : (3 : ℝ) ^ (-(m - 5)) * oscTop ≤
      M0 * ((3 : ℝ) ^ (-m) * global) := by
    have hsplit : (3 : ℝ) ^ (-(m - 5)) = (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-m) := by
      rw [← Real.rpow_natCast (3 : ℝ) 5, ← Real.rpow_add h3pos]
      congr 1
      push_cast
      ring
    have hstep : (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-m) * oscTop ≤
        (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-m) *
          (Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global) := by
      apply mul_le_mul_of_nonneg_left htop
      positivity
    have hratio : topWindowRatio d ≤ M0 := le_max_left _ _
    have hglobal0 : 0 ≤ (3 : ℝ) ^ (-m) * global := by positivity
    calc (3 : ℝ) ^ (-(m - 5)) * oscTop
        = (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-m) * oscTop := by rw [hsplit]
      _ ≤ (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-m) *
            (Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global) := hstep
      _ = topWindowRatio d * ((3 : ℝ) ^ (-m) * global) := by
          unfold topWindowRatio; ring
      _ ≤ M0 * ((3 : ℝ) ^ (-m) * global) :=
          mul_le_mul_of_nonneg_right hratio hglobal0
  -- the forcing leg
  have hlegData : 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
      ((3 : ℝ) ^ (m / 2) * data) ≤ M0 * ((3 : ℝ) ^ (m / 2) * data) := by
    have hsmall : (3 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1 := by
      rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by simp]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hcoef : 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential ≤ M0 := by
      have hle : 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential ≤
          5 / 2 * Kforce * exponential := by
        have h1 : 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 5 / 2 * Kforce := by
          nlinarith [Real.rpow_nonneg h3pos.le (-(5 / 2 : ℝ)), hKforce, hsmall]
        exact mul_le_mul_of_nonneg_right h1 hexponential
      exact hle.trans (le_max_right _ _)
    exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- combine the two legs
  have hbracket : (3 : ℝ) ^ (-(m - 5)) * oscTop +
      5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
        ((3 : ℝ) ^ (m / 2) * data) ≤
      M0 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data) := by
    have := add_le_add hlegTop hlegData
    calc _ ≤ M0 * ((3 : ℝ) ^ (-m) * global) + M0 * ((3 : ℝ) ^ (m / 2) * data) := this
      _ = M0 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data) := by ring
  -- absorb the exponential and the gap-power gain
  have hgap : (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4) ≤
      (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : 0 ≤ (1 - alpha) * (m - ell) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hbase : 0 ≤ (3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data := by
    positivity
  have hfinal : (3 : ℝ) ^ (-ell) * oscEll ≤
      rowOneConst d Cabs Kforce exponential *
        (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
        ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data) := by
    calc (3 : ℝ) ^ (-ell) * oscEll
        ≤ Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
            5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
              ((3 : ℝ) ^ (m / 2) * data)) := hfull
      _ ≤ Aexp * (M0 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) :=
          mul_le_mul_of_nonneg_left hbracket hAexp
      _ ≤ (Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4)) *
            (M0 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) := by
          apply mul_le_mul_of_nonneg_right habs
          exact mul_nonneg hM0nonneg hbase
      _ ≤ (Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2)) *
            (M0 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hM0nonneg hbase)
          exact mul_le_mul_of_nonneg_left hgap hCabs
      _ = rowOneConst d Cabs Kforce exponential *
            (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
            ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data) := by
          unfold rowOneConst
          rw [← hM0]
          ring
  exact Section6Holder.holderCampanato_rebase halpha hellm
    (by unfold rowOneConst; exact mul_nonneg hCabs hM0nonneg) hglobal hdata hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
