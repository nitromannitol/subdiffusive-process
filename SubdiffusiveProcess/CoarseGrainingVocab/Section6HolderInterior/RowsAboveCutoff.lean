import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneFinalStepFree
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoAtStepFree
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowThreeFree
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.SharedStoppingParameters

/-!
# The three frozen interior rows at one stopping scale (`m ≤ L`)

With all three rows now stated at free stopping parameters
(`RowOneFinalStepFree`, `RowTwoAtStepFree`, `RowThreeFree`), a single admissible
pair `(C₁, C₂)` serves all of them:

```text
  C₁ := max C₁ᵐⁱⁿ(row 1) C₁ᵐⁱⁿ(row 2)          (≥ 2, since row 2 forces it)
  C₂ := max (max C₂ᵐⁱⁿ(row 1) C₂ᵐⁱⁿ(row 2)) (max C₂ᵐⁱⁿ(row 3) C₁)
```

so that `2 ≤ C₁ ≤ C₂`, which by `SharedStoppingParameters` turns the three
model-free stopping conditions into theorems.  The three rows then assemble into
the frozen conclusion package at the *cutoff-independent* stopping carrier
`Section6Stopping.measurableHolderStoppingScale`, whose Γ₁ tail is already a
theorem (`UncutGammaOneTail.exists_uncutGammaOneTail`).

The deterministic margin is `step ≥ 21`, forced by row 2's two good-scale
selections.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The frozen interior conclusion package at the cutoff-independent stopping
carrier, for every `m ≤ L`.** -/
theorem exists_interiorRowsAboveCutoff (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ C1 C2 Cmin : ℝ, 2 ≤ C1 ∧ C1 ≤ C2 ∧ 0 ≤ Cmin ∧
      ∀ C : ℝ, Cmin ≤ C → ∀ step : ℕ, 21 ≤ step →
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ L m : ℕ, m ≤ L →
      ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
            (cube d m) u g →
        MemHolder (cube d m) (1 / 2) g →
        InteriorHolderRegularityConclusions M C L ω alpha m
          (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω) u g := by
  classical
  obtain ⟨C1min1, C2min1, Crow1, hC1min1, hC2min1, hCrow1, hrow1⟩ :=
    exists_interiorRowOneAtStepFree d hExcess
  obtain ⟨C1min2, C2min2, Crow2, hC1min2, hC12min2, hCrow2, hrow2⟩ :=
    exists_interiorRowTwoAtStepFree d hExcess
  obtain ⟨C2min3, Cmin3, hC2min3, hCmin3, hrow3⟩ :=
    exists_interiorRowThreeAtStepFree d hExcess
  set C1 : ℝ := max C1min1 C1min2 with hC1Def
  set C2 : ℝ := max (max C2min1 C2min2) (max C2min3 C1) with hC2Def
  have hC1two : (2 : ℝ) ≤ C1 := le_trans hC1min2 (le_max_right _ _)
  have hC1C2 : C1 ≤ C2 := le_trans (le_max_right C2min3 C1) (le_max_right _ _)
  have hC1thr1 : C1min1 ≤ C1 := le_max_left _ _
  have hC1thr2 : C1min2 ≤ C1 := le_max_right _ _
  have hC2thr1 : C2min1 ≤ C2 :=
    le_trans (le_max_left C2min1 C2min2) (le_max_left _ _)
  have hC2thr2 : C2min2 ≤ C2 :=
    le_trans (le_max_right C2min1 C2min2) (le_max_left _ _)
  have hC2thr3 : C2min3 ≤ C2 :=
    le_trans (le_max_left C2min3 C1) (le_max_right _ _)
  have hC1one : (1 : ℝ) ≤ C1 := by linarith
  refine ⟨C1, C2, max (max Crow1 Crow2) Cmin3, hC1two, hC1C2, ?_, ?_⟩
  · exact le_trans hCrow1 (le_trans (le_max_left _ _) (le_max_left _ _))
  intro C hCmin step hstep21 M hsmall alpha halpha hepsIcc hdelta L m hmL ω u g
    hsol hg
  obtain ⟨hlam0, hlam1, heps8⟩ :=
    holderStopping_conditions_of_coupled hC1two hC1C2 halpha
  have hCrow1C : Crow1 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCmin
  have hCrow2C : Crow2 ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCmin
  have hCmin3C : Cmin3 ≤ C := le_trans (le_max_right _ _) hCmin
  -- nonnegativity of the two right-hand-side brackets
  have htailPos : 0 < tailAverage M L m ω (cube d (m : ℤ)) := by
    rw [← tailCoefficientCubeAverage_eq_tailAverage_cube]
    exact tailCoefficientCubeAverage_pos M L m ω
  have hsem0 : 0 ≤ holderSeminormOn (cube d (m : ℤ)) (1 / 2) g :=
    Section6ExcessDecay.holderSeminormOn_nonneg hg
  refine interiorHolderRegularityConclusions_of_rows M C L ω alpha m _ u g
    ?_ ?_ ?_
  · -- row 1
    intro n hn x hx ell hell y hygrid hy
    have hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω : ℤ) ≤
        (m : ℤ) - (n : ℤ) := by omega
    have hrow := hrow1 C1 C2 hC1thr1 hC2thr1 step M hsmall alpha halpha hepsIcc
      hdelta heps8 hlam0 hlam1 L m hmL ω u g hsol hg n hstop x hx ell hell y
      hygrid hy
    refine hrow.trans ?_
    have hE0 : 0 ≤ normalizedL2On (cube d (m : ℤ))
        (fun z ↦ u.toFun z - averageOn (cube d (m : ℤ)) u.toFun) :=
      Section6Iteration.normalizedL2On_nonneg _ _
    have hD0 : 0 ≤ (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
        ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by
      have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (3 * (m : ℝ) / 2) :=
        Real.rpow_nonneg (by norm_num) _
      have h2 : (0 : ℝ) ≤ (tailAverage M L m ω (cube d (m : ℤ)))⁻¹ :=
        inv_nonneg.mpr htailPos.le
      positivity
    have hgap0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hswap : (tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
        (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
        holderSeminormOn (cube d (m : ℤ)) (1 / 2) g =
        (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
          ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by ring
    rw [hswap]
    have hbr : (0 : ℝ) ≤ normalizedL2On (cube d (m : ℤ))
          (fun z ↦ u.toFun z - averageOn (cube d (m : ℤ)) u.toFun) +
        (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
          ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by linarith
    have hstepmul : Crow1 * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) ≤
        C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hCrow1C hgap0
    exact mul_le_mul_of_nonneg_right hstepmul hbr
  · -- row 2
    intro n hn x hx
    have hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω : ℤ) ≤
        (m : ℤ) - (n : ℤ) := by omega
    have hrow := hrow2 C1 C2 hC1thr2 hC2thr2 hC1C2 step hstep21 M hsmall alpha
      halpha hepsIcc hdelta L m hmL ω u g hsol hg n hstop x hx
    refine hrow.trans ?_
    have hE0 : 0 ≤ vectorNormalizedL2On (cube d (m : ℤ))
        (fun z ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω z) • u.grad z) :=
      Real.sqrt_nonneg _
    have hD0 : 0 ≤ (tailAverage M L m ω (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
        (3 : ℝ) ^ ((m : ℝ) / 2) *
        holderSeminormOn (cube d (m : ℤ)) (1 / 2) g := by
      have h1 : (0 : ℝ) ≤ (tailAverage M L m ω (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) :=
        Real.rpow_nonneg htailPos.le _
      have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) :=
        Real.rpow_nonneg (by norm_num) _
      positivity
    have hgap0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hstepmul : Crow2 * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) ≤
        C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hCrow2C hgap0
    exact mul_le_mul_of_nonneg_right hstepmul (by linarith)
  · -- row 3
    intro n hn hwindow ell hnell hellm x hx
    exact hrow3 C2 hC2thr3 C1 hC1one C hCmin3C step M hsmall alpha halpha
      hepsIcc hdelta heps8 hlam1 L m hmL ω u g hsol hg n hn hwindow ell hnell
      hellm x hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
