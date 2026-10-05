module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneJoint
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneCarriers

@[expose] public section

/-!
# Boundary Holder row one: shared arithmetic

The boundary and interior Holder ladders have the same joint exponential
absorption and the same coefficient-average carriers.  The only difference in
the first row is the additional nonnegative boundary-datum slot.

This module reuses `Section6HolderInterior.interiorRowOne_combinedJoint` after
combining the forcing and boundary slots.  It keeps the two slots separate in
the conclusion, which is the shape consumed by the boundary theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

noncomputable section

/-- Statement row-one arithmetic with separate forcing and boundary-datum slots.
The constant is the gap-uniform `rowOneConstJoint`; no boundary-dependent
constant is introduced. -/
theorem boundaryRowOne_combinedJoint {d : ℕ}
    {alpha ell n m Aexp Cabs Kforce exponential oscEll oscTop global
      forcing boundary : ℝ}
    (halpha : alpha ≤ 1) (hell : ell ≤ n) (hnm : n ≤ m)
    (hglobal : 0 ≤ global) (hforcing : 0 ≤ forcing) (hboundary : 0 ≤ boundary)
    (hAexp : 0 ≤ Aexp) (hKforce : 0 ≤ Kforce) (hexp1 : 1 ≤ exponential)
    (hCabs : 1 ≤ Cabs)
    (habs : Aexp * exponential ≤
      Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 4))
    (htop : oscTop ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hshallow : m - ell ≤ 5 →
      oscEll ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hlong : 5 < m - ell →
      (3 : ℝ) ^ (-ell) * oscEll ≤
        Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
          5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
            ((3 : ℝ) ^ (m / 2) * (forcing + boundary)))) :
    (3 : ℝ) ^ (alpha * (n - ell)) * oscEll ≤
      rowOneConstJoint d Cabs Kforce * (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * forcing +
          (3 : ℝ) ^ (3 * m / 2) * boundary) := by
  have hdata : 0 ≤ forcing + boundary := add_nonneg hforcing hboundary
  have hmain := interiorRowOne_combinedJoint halpha hell hnm hglobal hdata hAexp
    hKforce hexp1 hCabs habs htop hshallow hlong
  simpa only [mul_add, add_assoc] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary
