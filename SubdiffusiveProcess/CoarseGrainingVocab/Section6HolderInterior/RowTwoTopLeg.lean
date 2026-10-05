module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoRatioRow

@[expose] public section

/-!
# Row 2's `hO` leg with Step 6's own tail average in front

`TopWindowEnergy.exists_interiorTopWindowOscillationEnergy` carries
`(b_{L,top+4})^{1/2}`, while interior Step 6's budget carries
`(b_{L,n+2})^{1/2}`.  Swapping them is the manuscript's `e.ratio.of.bs`, and the
price is `exp(C lambda (m-n))` — the same price the row-1 absorption converts
into a fraction of the frozen gap gain `3^{(1-alpha)(m-n)}` through the choice of
`C₁` ("using the choice of `C₁`").

This is the last *geometric/probabilistic* step of row 2's oscillation leg;
what remains after it is the Campanato family at the selected top and the
arithmetic of the absorption.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Both tail-average ratio directions at the two scales row 2 pairs. -/
theorem tail_pairing_at_top (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (C1 C2 alpha : ℝ) (step m n top L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hmL : m ≤ L) (hn2 : n + 2 ≤ m) (htop : top + 4 ≤ m)
    (hntop : n ≤ top)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha) :
    Real.sqrt (tailAverage M L (n + 2) omega (translatedCube d (n + 2 : ℕ) z)) *
        (Real.sqrt (tailAverage M L (top + 4) omega
          (translatedCube d (top + 4 : ℕ) z)))⁻¹ ≤
      Real.exp (ratioRate d *
        Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ))) := by
  obtain ⟨hcY, hc0⟩ := stoppedControls_pair M C1 C2 alpha step m n omega hstop
    z hzgrid hz
  have hs2 : Section6Stopping.holderStoppingS ≤ 1 / 2 := by
    rw [Section6Stopping.holderStoppingS]; norm_num
  have hlow := Section6Holder.stopped_tailAverage_ratio_bounds_exp
    (M := M) (L := L) (n := n) (q := n + 2) (m := m)
    hnm (by omega) (by omega) hmL
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha)
    hepsilon hs2 hlambda0 hlambda1 hdelta omega z hz hcY.1 hc0.1 hcY.2 hc0.2
  have hhigh := Section6Holder.stopped_tailAverage_ratio_bounds_exp
    (M := M) (L := L) (n := n) (q := top + 4) (m := m)
    hnm (by omega) (by omega) hmL
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha)
    hepsilon hs2 hlambda0 hlambda1 hdelta omega z hz hcY.1 hc0.1 hcY.2 hc0.2
  dsimp only at hlow hhigh
  have hsigmaTop : 0 < tailAverage M L (top + 4) omega
      (translatedCube d (top + 4 : ℕ) z) := by
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (top + 4)
      (translatePotentialSample z omega)
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  exact sqrt_tailAverage_pairing
    (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) hsigmaTop hb
    (Real.exp_nonneg _) hlow.1 hhigh.2

/-- **Row 2's oscillation leg with Step 6's tail average in front.** -/
theorem exists_interiorRowTwoTopLeg (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ C1 C2 alpha : ℝ,
        0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ≤ 1 →
        0 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ step L m n K : ℕ, m ≤ L →
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d ((m : ℤ) - 1) →
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        n + K + 5 ≤ m →
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1 →
      ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
        ∃ top : ℕ, n ≤ top ∧ top + 5 ≤ m ∧ m ≤ top + K + 5 ∧
          Real.sqrt (tailAverage M L (n + 2) omega
              (translatedCube d (n + 2 : ℕ) z)) *
              ((3 : ℝ) ^ (-(top : ℤ)) *
                normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
                  (fun p ↦ u.toFun p -
                    averageOn (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun)) ≤
            Real.exp (ratioRate d *
                Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ))) *
              (Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ))) *
              vectorNormalizedL2On (cube d (m : ℤ))
                (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
                  u.grad p) := by
  obtain ⟨Kosc, hKosc0, hleg⟩ := exists_interiorTopWindowOscillationEnergy d
  refine ⟨Kosc, hKosc0, ?_⟩
  intro M hsmall C1 C2 alpha heps0 heps1 hlam0 hlam1 hdelta step L m n K hmL
    omega z hzgrid hz hstop hwin hroom u
  obtain ⟨top, hntop, htopm, hmtop, hbound⟩ :=
    hleg M hsmall C1 C2 alpha heps0 heps1 step L m n K hmL omega z hzgrid hz
      hstop hwin hroom u
  refine ⟨top, hntop, htopm, hmtop, ?_⟩
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hz
  have hpair := tail_pairing_at_top M C1 C2 alpha step m n top L omega z hzgrid
    hzm hstop (by omega) hmL (by omega) (by omega) hntop hlam0 hlam1 heps0 hdelta
  have hcast : ((top + 4 : ℕ) : ℤ) = (top : ℤ) + 4 := by push_cast; ring
  rw [hcast] at hpair
  have hsigmaTop : 0 < tailAverage M L (top + 4) omega
      (translatedCube d ((top : ℤ) + 4) z) := by
    rw [← hcast, ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (top + 4)
      (translatePotentialSample z omega)
  have hrootpos : 0 < Real.sqrt (tailAverage M L (top + 4) omega
      (translatedCube d ((top : ℤ) + 4) z)) := Real.sqrt_pos.2 hsigmaTop
  set X : ℝ := (3 : ℝ) ^ (-(top : ℤ)) *
    normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
      (fun p ↦ u.toFun p -
        averageOn (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg (le_of_lt (zpow_pos (by norm_num) _))
      (Section6Iteration.normalizedL2On_nonneg _ _)
  have hsplit :
      Real.sqrt (tailAverage M L (n + 2) omega
          (translatedCube d (n + 2 : ℕ) z)) * X =
        (Real.sqrt (tailAverage M L (n + 2) omega
            (translatedCube d (n + 2 : ℕ) z)) *
          (Real.sqrt (tailAverage M L (top + 4) omega
            (translatedCube d ((top : ℤ) + 4) z)))⁻¹) *
          (Real.sqrt (tailAverage M L (top + 4) omega
            (translatedCube d ((top : ℤ) + 4) z)) * X) := by
    field_simp
  rw [hsplit]
  have hmul := mul_le_mul hpair hbound
    (mul_nonneg hrootpos.le hX0) (Real.exp_nonneg _)
  calc _ ≤ Real.exp (ratioRate d *
        Section6Stopping.holderStoppingLambda C1 alpha * ((m : ℝ) - (n : ℝ))) *
        (Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ)) *
          vectorNormalizedL2On (cube d (m : ℤ))
            (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
              u.grad p)) := hmul
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
