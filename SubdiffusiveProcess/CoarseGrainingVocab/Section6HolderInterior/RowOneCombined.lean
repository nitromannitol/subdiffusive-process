module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneShallow

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- **Frozen row 1 at every base scale**, from the deep-range Campanato output
and the shallow-range top-window transfer. -/
theorem interiorRowOne_combined {d : ℕ}
    {alpha ell n m Aexp Cabs Kforce exponential oscEll oscTop global data : ℝ}
    (halpha : alpha ≤ 1) (hell : ell ≤ n) (hnm : n ≤ m)
    (hglobal : 0 ≤ global) (hdata : 0 ≤ data)
    (hAexp : 0 ≤ Aexp) (hKforce : 0 ≤ Kforce) (hexponential : 0 ≤ exponential)
    (hCabs : 1 ≤ Cabs)
    (habs : Aexp ≤ Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4))
    (htop : oscTop ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hshallow : m - ell ≤ 5 →
      oscEll ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hlong : 5 < m - ell →
      (3 : ℝ) ^ (-ell) * oscEll ≤
        Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
          5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
            ((3 : ℝ) ^ (m / 2) * data))) :
    (3 : ℝ) ^ (alpha * (n - ell)) * oscEll ≤
      rowOneConst d Cabs Kforce exponential * (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by
  have hCabs0 : 0 ≤ Cabs := by linarith
  have hM0 : 0 ≤ max (topWindowRatio d) (5 / 2 * Kforce * exponential) :=
    le_trans (topWindowRatio_nonneg d) (le_max_left _ _)
  by_cases hgap : m - ell ≤ 5
  · -- shallow: the top-window transfer alone, at constant `topWindowRatio d`
    refine le_trans (interiorRowOne_shallow halpha hell hnm hgap hglobal hdata
      (hshallow hgap)) ?_
    have hbase : 0 ≤ (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by positivity
    have hconst : topWindowRatio d ≤ rowOneConst d Cabs Kforce exponential := by
      unfold rowOneConst
      calc topWindowRatio d
          ≤ max (topWindowRatio d) (5 / 2 * Kforce * exponential) :=
            le_max_left _ _
        _ = 1 * max (topWindowRatio d) (5 / 2 * Kforce * exponential) := by ring
        _ ≤ Cabs * max (topWindowRatio d) (5 / 2 * Kforce * exponential) :=
            mul_le_mul_of_nonneg_right hCabs hM0
    calc topWindowRatio d * (3 : ℝ) ^ (-alpha * (m - n)) *
          (global + (3 : ℝ) ^ (3 * m / 2) * data)
        = topWindowRatio d * ((3 : ℝ) ^ (-alpha * (m - n)) *
            (global + (3 : ℝ) ^ (3 * m / 2) * data)) := by ring
      _ ≤ rowOneConst d Cabs Kforce exponential *
            ((3 : ℝ) ^ (-alpha * (m - n)) *
              (global + (3 : ℝ) ^ (3 * m / 2) * data)) :=
          mul_le_mul_of_nonneg_right hconst hbase
      _ = rowOneConst d Cabs Kforce exponential *
            (3 : ℝ) ^ (-alpha * (m - n)) *
            (global + (3 : ℝ) ^ (3 * m / 2) * data) := by ring
  · -- deep: the Campanato passage
    push Not at hgap
    exact interiorRowOne_arith halpha (by linarith) hglobal hdata hAexp hKforce
      hexponential hCabs0 habs htop (hlong hgap)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
