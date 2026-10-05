module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoRatioScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoRatioScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.TopWindowEnergy

@[expose] public section

/-!
# The top-window leg with the Step-6 tail average read at a free scale

`RowTwoTopLeg.exists_interiorRowTwoTopLeg` carries the tail average at `n + 2`,
the scale interior Step 6 would use if its good event sat at the frozen base
scale.  The good event actually available at a grid centre is at a **selected**
scale, so the gate is run there and its `sigma` is read at `gate + 2`.

This module is the same composition with that scale left free: the pairing of
`RowTwoRatioScales.sqrt_tailAverage_pairing_at_cut` replaces
`RowTwoTopLeg.tail_pairing_at_top`, and nothing else changes.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **Row 2's oscillation leg against the global energy, with the tail average
read at a free scale `p`.** -/
theorem exists_interiorRowTwoTopLegAt_cut (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ C1 C2 alpha : ℝ,
        0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ≤ 1 →
        0 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ step L m n K p : ℕ, ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d ((m : ℤ) - 1) →
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        n + K + 5 ≤ m →
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1 →
        n < m → n ≤ p → p ≤ m →
      ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
        ∃ top : ℕ, n ≤ top ∧ top + 5 ≤ m ∧ m ≤ top + K + 5 ∧
          Real.sqrt (tailAverage M L p omega (translatedCube d (p : ℕ) z)) *
              ((3 : ℝ) ^ (-(top : ℤ)) *
                normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
                  (fun q ↦ u.toFun q -
                    averageOn (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun)) ≤
            rowTwoRatioBound_cut d C1 alpha m n *
              (Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ))) *
              vectorNormalizedL2On (cube d (m : ℤ))
                (fun q ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega q) •
                  u.grad q) := by
  obtain ⟨Kosc, hKosc0, hleg⟩ := exists_interiorTopWindowOscillationEnergy_cut d
  refine ⟨Kosc, hKosc0, ?_⟩
  intro M hsmall C1 C2 alpha heps0 heps1 hlam0 hlam1 hdelta step L m n K p
    omega z hzgrid hz hstop hwin hroom hnm hnp hpm u
  obtain ⟨top, hntop, htopm, hmtop, hbound⟩ :=
    hleg M hsmall C1 C2 alpha heps0 heps1 step L m n K omega z hzgrid hz
      hstop hwin hroom u
  refine ⟨top, hntop, htopm, hmtop, ?_⟩
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hz
  have hpair := sqrt_tailAverage_pairing_at_cut M C1 C2 alpha step m n p (top + 4) L
    omega z z hzgrid hzm hzgrid hzm hstop hnm hnp hpm (by omega) (by omega)
    hlam0 hlam1 heps0 hdelta
  have hcast : ((top + 4 : ℕ) : ℤ) = (top : ℤ) + 4 := by push_cast; ring
  rw [hcast] at hpair
  have hsigmaTop : 0 < tailAverage M L (top + 4) omega
      (translatedCube d ((top : ℤ) + 4) z) := by
    rw [← hcast]
    exact tailAverage_translatedCube_pos_cut M L (top + 4) omega z
  have hrootpos : 0 < Real.sqrt (tailAverage M L (top + 4) omega
      (translatedCube d ((top : ℤ) + 4) z)) := Real.sqrt_pos.2 hsigmaTop
  set X : ℝ := (3 : ℝ) ^ (-(top : ℤ)) *
    normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
      (fun q ↦ u.toFun q -
        averageOn (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg (le_of_lt (zpow_pos (by norm_num) _))
      (Section6Iteration.normalizedL2On_nonneg _ _)
  have hsplit :
      Real.sqrt (tailAverage M L p omega (translatedCube d (p : ℕ) z)) * X =
        (Real.sqrt (tailAverage M L p omega (translatedCube d (p : ℕ) z)) *
          (Real.sqrt (tailAverage M L (top + 4) omega
            (translatedCube d ((top : ℤ) + 4) z)))⁻¹) *
          (Real.sqrt (tailAverage M L (top + 4) omega
            (translatedCube d ((top : ℤ) + 4) z)) * X) := by
    field_simp
  rw [hsplit]
  have hmul := mul_le_mul hpair hbound
    (mul_nonneg hrootpos.le hX0) (rowTwoRatioBound_nonneg_cut d C1 alpha m n)
  calc _ ≤ rowTwoRatioBound_cut d C1 alpha m n *
        (Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ)) *
          vectorNormalizedL2On (cube d (m : ℤ))
            (fun q ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega q) •
              u.grad q)) := hmul
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
