import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.RowThreeFromGrid

/-!
# Boundary Holder row three: scalar long-grid recombination

This is the OPEN-17-stable arithmetic seam.  The stopped iteration supplies a
common prefactor multiplying the excess, oscillation, and datum-bearing defect
rows; the three explicit coefficient budgets below convert it to the exact
long-grid contract consumed by `boundaryRowThree_of_grid`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Recombine the three scalar budgets of the datum-bearing stopped recurrence
into the literal long-grid estimate. -/
theorem boundaryRowThree_gridCore
    {X pref thetaCoeff oscCoeff defect exTop oscTop : ℝ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {C alpha : ℝ} {L m n ell : ℕ}
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d} {x : Vec d}
    {h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hraw : X ≤ pref * (thetaCoeff * exTop + oscCoeff * oscTop + defect))
    (hexTop : 0 ≤ exTop) (hoscTop : 0 ≤ oscTop)
    (hfirst : pref * thetaCoeff ≤
      C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) /
        holderOffGridOuterFactor d ^ 2)
    (hsecond : pref * oscCoeff ≤
      C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) /
        (holderOffGridOuterFactor d * holderOffGridOscillationFactor d))
    (hthird : pref * defect ≤
      (C * (tailAverage M L m omega (cube d m))⁻¹ *
          (3 : ℝ) ^ ((ell : ℝ) / 2) *
          holderSeminormOn (cube d m) (1 / 2) g +
        (if x ∈ cube d (m - 1) then 0 else
          C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
              vectorSupNormOn (cube d m) h.grad +
            (3 : ℝ) ^ ((ell : ℝ) / 2) *
              fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                (1 / 2) h.grad))) /
        holderOffGridOuterFactor d) :
    X ≤
      (C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) /
          holderOffGridOuterFactor d ^ 2) * exTop +
      (C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) /
          (holderOffGridOuterFactor d * holderOffGridOscillationFactor d)) * oscTop +
      (C * (tailAverage M L m omega (cube d m))⁻¹ *
          (3 : ℝ) ^ ((ell : ℝ) / 2) *
          holderSeminormOn (cube d m) (1 / 2) g +
        (if x ∈ cube d (m - 1) then 0 else
          C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
              vectorSupNormOn (cube d m) h.grad +
            (3 : ℝ) ^ ((ell : ℝ) / 2) *
              fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                (1 / 2) h.grad))) /
        holderOffGridOuterFactor d := by
  exact holderStepSevenGrid_of_threeBudgets hexTop hoscTop hraw hfirst hsecond hthird

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
