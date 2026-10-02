import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneCarriers




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The gap-uniform row-1 constant. -/
def rowOneConstJoint (d : ℕ) (Cabs Kforce : ℝ) : ℝ :=
  Cabs * max (topWindowRatio d) (5 / 2 * Kforce)

theorem rowOneConstJoint_nonneg (d : ℕ) {Cabs Kforce : ℝ} (hCabs : 0 ≤ Cabs) :
    0 ≤ rowOneConstJoint d Cabs Kforce :=
  mul_nonneg hCabs (le_trans (topWindowRatio_nonneg d) (le_max_left _ _))

/-- **Row 1 in the deep range, with a gap-uniform constant.** -/
theorem interiorRowOne_arithJoint {d : ℕ}
    {alpha ell n m Aexp Cabs Kforce exponential oscEll oscTop global data : ℝ}
    (halpha : alpha ≤ 1) (hellm : ell ≤ m)
    (hglobal : 0 ≤ global) (hdata : 0 ≤ data)
    (hAexp : 0 ≤ Aexp) (hKforce : 0 ≤ Kforce) (hexp1 : 1 ≤ exponential)
    (hCabs : 0 ≤ Cabs)
    (habs : Aexp * exponential ≤ Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4))
    (htop : oscTop ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hfull : (3 : ℝ) ^ (-ell) * oscEll ≤
      Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
        5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
          ((3 : ℝ) ^ (m / 2) * data))) :
    (3 : ℝ) ^ (alpha * (n - ell)) * oscEll ≤
      rowOneConstJoint d Cabs Kforce * (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hexp0 : (0 : ℝ) ≤ exponential := by linarith
  set M1 : ℝ := max (topWindowRatio d) (5 / 2 * Kforce) with hM1
  have hM1nonneg : 0 ≤ M1 := le_trans (topWindowRatio_nonneg d) (le_max_left _ _)
  have hGlobal0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-m) * global := by positivity
  have hData0 : (0 : ℝ) ≤ (3 : ℝ) ^ (m / 2) * data := by positivity
  -- leg 1: the top window, no `exponential` needed
  have hleg1 : (3 : ℝ) ^ (-(m - 5)) * oscTop ≤ M1 * ((3 : ℝ) ^ (-m) * global) := by
    have hsplit : (3 : ℝ) ^ (-(m - 5)) = (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-m) := by
      rw [← Real.rpow_natCast (3 : ℝ) 5, ← Real.rpow_add h3pos]
      congr 1; push_cast; ring
    calc (3 : ℝ) ^ (-(m - 5)) * oscTop
        = (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-m) * oscTop := by rw [hsplit]
      _ ≤ (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-m) *
            (Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global) := by
          apply mul_le_mul_of_nonneg_left htop; positivity
      _ = topWindowRatio d * ((3 : ℝ) ^ (-m) * global) := by
          unfold topWindowRatio; ring
      _ ≤ M1 * ((3 : ℝ) ^ (-m) * global) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hGlobal0
  -- leg 2: the forcing, carrying `exponential`
  have hleg2 : 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
      ((3 : ℝ) ^ (m / 2) * data) ≤
        exponential * (M1 * ((3 : ℝ) ^ (m / 2) * data)) := by
    have hsmall : (3 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1 := by
      rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by simp]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hcoef : 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ M1 := by
      have h1 : 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 5 / 2 * Kforce := by
        nlinarith [Real.rpow_nonneg h3pos.le (-(5 / 2 : ℝ)), hKforce, hsmall]
      exact h1.trans (le_max_right _ _)
    calc 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
          ((3 : ℝ) ^ (m / 2) * data)
        = (5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ))) *
            (exponential * ((3 : ℝ) ^ (m / 2) * data)) := by ring
      _ ≤ M1 * (exponential * ((3 : ℝ) ^ (m / 2) * data)) := by
          apply mul_le_mul_of_nonneg_right hcoef
          exact mul_nonneg hexp0 hData0
      _ = exponential * (M1 * ((3 : ℝ) ^ (m / 2) * data)) := by ring
  -- the bracket, with `exponential` pulled out
  have hbracket : (3 : ℝ) ^ (-(m - 5)) * oscTop +
      5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
        ((3 : ℝ) ^ (m / 2) * data) ≤
      exponential * (M1 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) := by
    have hfirst : M1 * ((3 : ℝ) ^ (-m) * global) ≤
        exponential * (M1 * ((3 : ℝ) ^ (-m) * global)) := by
      nlinarith [mul_nonneg hM1nonneg hGlobal0, hexp1]
    calc _ ≤ M1 * ((3 : ℝ) ^ (-m) * global) +
            exponential * (M1 * ((3 : ℝ) ^ (m / 2) * data)) := add_le_add hleg1 hleg2
      _ ≤ exponential * (M1 * ((3 : ℝ) ^ (-m) * global)) +
            exponential * (M1 * ((3 : ℝ) ^ (m / 2) * data)) := by linarith
      _ = exponential * (M1 * ((3 : ℝ) ^ (-m) * global +
            (3 : ℝ) ^ (m / 2) * data)) := by ring
  -- absorb the joint exponential
  have hbase : 0 ≤ (3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data := by
    positivity
  have hgap : (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4) ≤
      (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : 0 ≤ (1 - alpha) * (m - ell) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hfinal : (3 : ℝ) ^ (-ell) * oscEll ≤
      rowOneConstJoint d Cabs Kforce *
        (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
        ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data) := by
    calc (3 : ℝ) ^ (-ell) * oscEll
        ≤ Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
            5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
              ((3 : ℝ) ^ (m / 2) * data)) := hfull
      _ ≤ Aexp * (exponential *
            (M1 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data))) :=
          mul_le_mul_of_nonneg_left hbracket hAexp
      _ = (Aexp * exponential) *
            (M1 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) := by ring
      _ ≤ (Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4)) *
            (M1 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) := by
          apply mul_le_mul_of_nonneg_right habs
          exact mul_nonneg hM1nonneg hbase
      _ ≤ (Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2)) *
            (M1 * ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hM1nonneg hbase)
          exact mul_le_mul_of_nonneg_left hgap hCabs
      _ = rowOneConstJoint d Cabs Kforce *
            (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
            ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data) := by
          unfold rowOneConstJoint; rw [← hM1]; ring
  exact Section6Holder.holderCampanato_rebase halpha hellm
    (rowOneConstJoint_nonneg d hCabs) hglobal hdata hfinal

/-- **Frozen row 1 at every base scale, with a gap-uniform constant.** -/
theorem interiorRowOne_combinedJoint {d : ℕ}
    {alpha ell n m Aexp Cabs Kforce exponential oscEll oscTop global data : ℝ}
    (halpha : alpha ≤ 1) (hell : ell ≤ n) (hnm : n ≤ m)
    (hglobal : 0 ≤ global) (hdata : 0 ≤ data)
    (hAexp : 0 ≤ Aexp) (hKforce : 0 ≤ Kforce) (hexp1 : 1 ≤ exponential)
    (hCabs : 1 ≤ Cabs)
    (habs : Aexp * exponential ≤ Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4))
    (htop : oscTop ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hshallow : m - ell ≤ 5 →
      oscEll ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hlong : 5 < m - ell →
      (3 : ℝ) ^ (-ell) * oscEll ≤
        Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
          5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
            ((3 : ℝ) ^ (m / 2) * data))) :
    (3 : ℝ) ^ (alpha * (n - ell)) * oscEll ≤
      rowOneConstJoint d Cabs Kforce * (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by
  have hCabs0 : 0 ≤ Cabs := by linarith
  have hM1 : 0 ≤ max (topWindowRatio d) (5 / 2 * Kforce) :=
    le_trans (topWindowRatio_nonneg d) (le_max_left _ _)
  by_cases hgap : m - ell ≤ 5
  · refine le_trans (interiorRowOne_shallow halpha hell hnm hgap hglobal hdata
      (hshallow hgap)) ?_
    have hbase : 0 ≤ (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by positivity
    have hconst : topWindowRatio d ≤ rowOneConstJoint d Cabs Kforce := by
      unfold rowOneConstJoint
      calc topWindowRatio d ≤ max (topWindowRatio d) (5 / 2 * Kforce) :=
            le_max_left _ _
        _ = 1 * max (topWindowRatio d) (5 / 2 * Kforce) := by ring
        _ ≤ Cabs * max (topWindowRatio d) (5 / 2 * Kforce) :=
            mul_le_mul_of_nonneg_right hCabs hM1
    calc topWindowRatio d * (3 : ℝ) ^ (-alpha * (m - n)) *
          (global + (3 : ℝ) ^ (3 * m / 2) * data)
        = topWindowRatio d * ((3 : ℝ) ^ (-alpha * (m - n)) *
            (global + (3 : ℝ) ^ (3 * m / 2) * data)) := by ring
      _ ≤ rowOneConstJoint d Cabs Kforce *
            ((3 : ℝ) ^ (-alpha * (m - n)) *
              (global + (3 : ℝ) ^ (3 * m / 2) * data)) :=
          mul_le_mul_of_nonneg_right hconst hbase
      _ = rowOneConstJoint d Cabs Kforce * (3 : ℝ) ^ (-alpha * (m - n)) *
            (global + (3 : ℝ) ^ (3 * m / 2) * data) := by ring
  · push_neg at hgap
    exact interiorRowOne_arithJoint halpha (by linarith) hglobal hdata hAexp
      hKforce hexp1 hCabs0 habs htop (hlong hgap)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
