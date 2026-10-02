import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.AmbientOffGridRows

/-!
# Theta ladder: rebasing stopped rows at a variable top

The recurrence is printed relative to `m-2` and the off-grid restriction uses
one further scale.  Rebasing at `m-J` leaves exactly the fixed `J-3` factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- Rebase one stopped off-grid row at `top = m-J`. -/
theorem offGridStoppedRow_rebase_variableTop
    {d m J s : ℕ} (hJm : J ≤ m)
    {K Budget X : ℝ}
    (hrow : X ≤ Real.sqrt ((3 : ℝ) ^ d) *
      (K * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
        (((m : ℝ) - 2) - ((s : ℝ) + 1))) * Budget)) :
    X ≤
      (Real.sqrt ((3 : ℝ) ^ d) * K *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((J : ℝ) - 3))) * Budget *
          (3 : ℝ) ^ (-(1 / 2 : ℝ) *
            (((m - J : ℕ) : ℝ) - (s : ℝ))) := by
  have hcast : ((m - J : ℕ) : ℝ) = (m : ℝ) - (J : ℝ) :=
    Nat.cast_sub hJm
  have hexponent :
      -(1 / 2 : ℝ) * (((m : ℝ) - 2) - ((s : ℝ) + 1)) =
        -(1 / 2 : ℝ) * ((J : ℝ) - 3) +
          -(1 / 2 : ℝ) * (((m - J : ℕ) : ℝ) - (s : ℝ)) := by
    rw [hcast]
    ring
  rw [hexponent, Real.rpow_add (by norm_num : (0 : ℝ) < 3)] at hrow
  nlinarith only [hrow]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
