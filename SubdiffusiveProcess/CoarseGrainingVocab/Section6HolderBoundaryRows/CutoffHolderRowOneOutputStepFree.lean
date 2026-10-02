import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.RowOneOutputStepFree
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffCampanatoFull
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.RowOneOutputStep
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff.V4Contraction
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.CampanatoFull
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowOneInstantiation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.StoppingWindows
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.RowOneBoundaryBudget
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneGate
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneInstantiation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneShapeMatch
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoAbsorb




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderBelow

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The linear-exponential absorption used by the boundary row is monotone in
the inverse stopping parameter. -/
theorem holderLinearExponentialAbsorption_mono {A0 P C1 C1' C : ℝ}
    (hP : 0 ≤ P) (hC1 : 0 < C1) (hle : C1 ≤ C1')
    (h : ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
      (1 + C1⁻¹ * (1 - alpha) * gap) *
          Real.exp (A0 + P * (C1⁻¹ * (1 - alpha)) * (gap + 1)) ≤
        C * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) :
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
      (1 + C1'⁻¹ * (1 - alpha) * gap) *
          Real.exp (A0 + P * (C1'⁻¹ * (1 - alpha)) * (gap + 1)) ≤
        C * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.holderLinearExponentialAbsorption_mono (A0 := A0) (P := P) (C1 := C1) (C1' := C1') (C := C) (hP := hP) (hC1 := hC1) (hle := hle) (h := h)

/-- The deep-branch boundary row-one output at arbitrary admissible stopping
parameters. -/
theorem exists_boundaryCampanatoOutputAtStepFree_cut (d : ℕ) [NeZero d]
    (hExcess : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ (C1min C2min Cabs Kdata : ℝ), 1 ≤ C1min ∧ 1 ≤ C2min ∧ 1 ≤ Cabs ∧
      0 ≤ Kdata ∧
      ∀ C1 C2 : ℝ, C1min ≤ C1 → C2min ≤ C2 → ∀ step : ℕ,
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤
          Section6Stopping.holderStoppingLambda C1 alpha →
        0 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
      ∀ L m : ℕ, L < m →
      ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
          (originCube d (m : ℤ)) u h g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
      ∀ n : ℕ,
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
      ∀ x : Vec d, x ∈ cube d (m : ℤ) →
      ∀ ell : ℕ, ell ≤ n → 5 < (m : ℝ) - (ell : ℝ) →
      ∀ y : Vec d, OnTriadicGrid ell y → y ∈ truncatedCube d (m : ℤ) (n : ℤ) x →
        ∃ Aexp exponential : ℝ, 0 ≤ Aexp ∧ 1 ≤ exponential ∧
          Aexp * exponential ≤
            Cabs * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (ell : ℝ)) / 4) ∧
          (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
                (fun p => u.toFun p -
                  averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
            Aexp * ((3 : ℝ) ^ (-((m : ℝ) - 5)) *
                normalizedL2On (truncatedCube d (m : ℤ) ((m : ℤ) - 5) y)
                  (fun p => u.toFun p -
                    averageOn (truncatedCube d (m : ℤ) ((m : ℤ) - 5) y) u.toFun) +
              5 / 2 * Kdata * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
                ((3 : ℝ) ^ ((m : ℝ) / 2) *
                  ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
                      holderSeminormOn (cube d (m : ℤ)) (1 / 2) g +
                    (if x ∈ cube d ((m : ℤ) - 1) then 0 else
                      fractionalInfinityNormOnReal (cube d (m : ℤ))
                        ((3 : ℝ) ^ (m : ℤ)) (1 / 2) h.grad)))) := by
  classical
  obtain ⟨Cstep, K, Citer, hCstep, hK, hCiter, hcamp⟩ :=
    Section6HolderLift.exists_boundaryRowTwoCutoffCampanatoFull d hExcess
  obtain ⟨k, C2min, hk, hC2min, hth⟩ :=
    exists_boundaryHolderContractionParameters_cut d Cstep hCstep
  obtain ⟨hthetaIoo, hthetak, hcontract⟩ := hth
  set Keps : ℝ := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K with hKepsDef
  set Kforce : ℝ := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
    with hKforceDef
  set Kmean : ℝ := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) with hKmeanDef
  set Kboundary : ℝ := Cstep * (1 / 4 : ℝ) ^ (-3 : ℤ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) with hKboundaryDef
  set Aforce : ℝ := 5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) with hAforceDef
  set Amean : ℝ := Kmean * (3 * Keps) with hAmeanDef
  set Abound : ℝ := 5 / 2 * Kboundary * (3 : ℝ) ^ (-(5 / 2 : ℝ))
    with hAboundDef
  set Kbudget : ℝ := max Aforce (max Amean Abound) with hKbudgetDef
  set Kdata : ℝ := (6 / 5 : ℝ) * (3 : ℝ) ^ (5 / 2 : ℝ) * Kbudget
    with hKdataDef
  have hKeps0 : 0 ≤ Keps := by rw [hKepsDef]; positivity
  have hKforce0 : 0 ≤ Kforce := by
    have := Section6ExcessDecay.fractionalHolderConst_nonneg d
    rw [hKforceDef]
    positivity
  have hKmean0 : 0 ≤ Kmean := by rw [hKmeanDef]; positivity
  have hKboundary0 : 0 ≤ Kboundary := by rw [hKboundaryDef]; positivity
  have hAforce0 : 0 ≤ Aforce := by rw [hAforceDef]; positivity
  have hAmean0 : 0 ≤ Amean := by rw [hAmeanDef]; positivity
  have hAbound0 : 0 ≤ Abound := by rw [hAboundDef]; positivity
  have hKbudget0 : 0 ≤ Kbudget := hAforce0.trans (by
    rw [hKbudgetDef]
    exact le_max_left _ _)
  have hKdata0 : 0 ≤ Kdata := by rw [hKdataDef]; positivity
  have hKdataCoeff :
      5 / 2 * Kdata * (3 : ℝ) ^ (-(5 / 2 : ℝ)) = 3 * Kbudget := by
    rw [hKdataDef]
    have hpow : (3 : ℝ) ^ (5 / 2 : ℝ) * (3 : ℝ) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    calc
      5 / 2 * ((6 / 5 : ℝ) * (3 : ℝ) ^ (5 / 2 : ℝ) * Kbudget) *
          (3 : ℝ) ^ (-(5 / 2 : ℝ)) =
        3 * ((3 : ℝ) ^ (5 / 2 : ℝ) * (3 : ℝ) ^ (-(5 / 2 : ℝ))) *
          Kbudget := by ring
      _ = 3 * Kbudget := by rw [hpow]; ring
  set A0 : ℝ := Citer * ((k : ℝ) + 1) * ((k : ℝ) + 2) with hA0Def
  set P : ℝ := Citer * ((k : ℝ) + 1) + 3 * Citer * Keps + ratioRate_cut d with hPDef
  have hP0 : 0 ≤ P := by
    have := ratioRate_nonneg_cut d
    rw [hPDef]
    positivity
  obtain ⟨C1abs, Cabs, hC1abs, hCabs, habsorb⟩ :=
    Section6Holder.exists_holderLinearExponentialAbsorption A0 P hP0
  refine ⟨max C1abs 1, C2min, max Cabs 1, Kdata, le_max_right _ _, hC2min,
    le_max_right _ _, hKdata0, ?_⟩
  intro C1 C2 hC1thr hC2ge step M hsmall alpha halpha hepsIcc hdelta heps8
    hlam0 hlam1 L m hmL ω u h g
    hsol hg hh n hstop x hx ell hell hdeep y hygrid hy
  have hC1pos : (0 : ℝ) < C1 := lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_right C1abs 1) hC1thr)
  have hC2 : (1 : ℝ) ≤ C2 := le_trans hC2min hC2ge
  have habsorbC1 := holderLinearExponentialAbsorption_mono hP0 hC1abs
    (le_trans (le_max_left C1abs 1) hC1thr) habsorb
  have hycube : y ∈ cube d (m : ℤ) := rowOne_centre_mem hy
  have hnm5 : (n : ℤ) ≤ (m : ℤ) - 5 :=
    base_scale_le_of_stopping_cut M alpha _ _ step m n ω hstop
  obtain ⟨htoplt, htople⟩ := rowOne_base_lt_top hnm5 hell hdeep
  have hstopEll := rowOne_stopping_at_base_cut M alpha _ _ step m n ell ω hstop hell
  obtain ⟨hctrlY, _hctrl0⟩ :=
    Section6HolderBelowCutoff.Rows.stoppedControls_pair_cut M C1 C2 alpha step m ell ω hstopEll y hygrid hycube
  have hepsPos : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha := by
    rw [Section6Stopping.holderStoppingEpsilon]
    have hC2pos : (0 : ℝ) < C2 := by linarith
    positivity
  have hratio := stoppedRatio_row_cut (L := L) M C1 C2 alpha step m ell (m - 5) ω
    (by omega) (by omega) hlam0 hlam1 hepsPos hdelta y hycube hstopEll hygrid
  have hepsC2 : Section6Stopping.holderStoppingEpsilon C2 alpha ≤ C2min⁻¹ := by
    rw [Section6Stopping.holderStoppingEpsilon]
    have hC2minpos : (0 : ℝ) < C2min := by linarith
    have hC2pos : (0 : ℝ) < C2 := by linarith
    have hsq : Real.sqrt (1 - alpha) ≤ 1 := by
      have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith [halpha.1]
      simpa using Real.sqrt_le_sqrt h1
    have hinv : (0 : ℝ) ≤ C2⁻¹ := by positivity
    have hmono : C2⁻¹ ≤ C2min⁻¹ := inv_anti₀ hC2minpos hC2ge
    calc C2⁻¹ * Real.sqrt (1 - alpha) ≤ C2⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hsq hinv
      _ = C2⁻¹ := by ring
      _ ≤ C2min⁻¹ := hmono
  have hcontr := hcontract (Section6Stopping.holderStoppingEpsilon C2 alpha)
    hepsPos hepsC2
  have hcontrOld :
      Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
            Section6Stopping.holderStoppingEpsilon C2 alpha) ≤
        ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
    have hamp : 0 ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by positivity
    have hbase : 0 ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := by positivity
    norm_num only [show (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) = 8 by norm_num,
      show (1 / 4 : ℝ) ^ (-2 : ℝ) = 16 by norm_num] at hcontr ⊢
    nlinarith only [hcontr, mul_nonneg hCstep.le (mul_nonneg hamp hepsPos)]
  let ratioExponential := Real.exp (ratioRate_cut d *
    Section6Stopping.holderStoppingLambda C1 alpha * ((m : ℝ) - (ell : ℝ)))
  have hout := hcamp M hsmall (Section6Stopping.holderStoppingEpsilon C2 alpha)
    hepsIcc (Section6Stopping.holderStoppingLambda C1 alpha) hlam0 hdelta heps8
    k hk ((3 : ℝ) ^ (-(1 / 4 : ℝ))) hthetaIoo hthetak hcontrOld
    L m ell (m - 5) htoplt htople y hycube ω hctrlY.1 hctrlY.2
    ratioExponential (Real.exp_nonneg _) hratio u h g hsol hg hh
  dsimp only at hout
  let gap : ℝ := (m : ℝ) - (ell : ℝ)
  let lambda : ℝ := Section6Stopping.holderStoppingLambda C1 alpha
  let boundaryTop : ℝ :=
    if BoundaryTouches (truncatedCube d (m : ℤ) ((m - 5 : ℕ) : ℤ) y)
        (cube d (m : ℤ)) then 1 else 0
  let outsideIndicator : ℝ := if x ∈ cube d ((m : ℤ) - 1) then 0 else 1
  let forcing : ℝ := (tailCoefficientCubeAverage M L m ω)⁻¹ *
    holderSeminormOn (cube d (m : ℤ)) (1 / 2) g
  have hgap0 : 0 ≤ gap := by dsimp only [gap]; linarith
  have hratio1 : 1 ≤ ratioExponential := by
    have hx0 : 0 ≤ ratioRate_cut d * lambda * gap := by
      exact mul_nonneg (mul_nonneg (ratioRate_nonneg_cut d) hlam0) hgap0
    simpa only [ratioExponential, lambda, gap, Real.exp_zero] using
      Real.exp_le_exp.mpr hx0
  have hforcing0 : 0 ≤ forcing := by
    dsimp only [forcing]
    exact mul_nonneg (inv_nonneg.mpr (tailCoefficientCubeAverage_pos M L m ω).le)
      (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  have hboundaryTop0 : 0 ≤ boundaryTop := by
    dsimp only [boundaryTop]
    split_ifs <;> norm_num
  have houtside0 : 0 ≤ outsideIndicator := by
    dsimp only [outsideIndicator]
    split_ifs <;> norm_num
  have hindicator : boundaryTop ≤ outsideIndicator := by
    dsimp only [boundaryTop, outsideIndicator]
    exact Section6Holder.boundaryIndicator_top_le_not_interior hy
      (by omega : (n : ℤ) ≤ ((m - 5 : ℕ) : ℤ)) (by omega)
  have hbudget := Section6HolderBoundary.boundaryRowOne_dataBudget_le_fractionalInfinityNormOn
    (K := Kbudget) (Aforce := Aforce) (Amean := Amean) (Abound := Abound)
    (lambda := lambda) (gap := gap) (exponential := ratioExponential)
    (forcing := forcing) (boundaryIndicator := boundaryTop)
    (outsideIndicator := outsideIndicator) hh
    hKbudget0 hAmean0 hAbound0
    (by rw [hKbudgetDef]; apply le_max_left)
    (by rw [hKbudgetDef]; exact le_max_of_le_right (le_max_left _ _))
    (by rw [hKbudgetDef]; exact le_max_of_le_right (le_max_right _ _))
    hlam0 hlam1.le hgap0 hratio1 hforcing0 hboundaryTop0 houtside0 hindicator
  rw [← hKepsDef, ← hKforceDef, ← hKboundaryDef] at hout
  have hm5 : 5 ≤ m := by omega
  have htopCast : ((m - 5 : ℕ) : ℤ) = (m : ℤ) - 5 := by omega
  have htopReal : ((m - 5 : ℕ) : ℝ) = (m : ℝ) - 5 := by
    rw [Nat.cast_sub hm5]
    norm_num
  have hDbudget :
      5 / 2 * Kforce * (3 : ℝ) ^ (-(((m : ℝ) - ((m - 5 : ℕ) : ℝ)) / 2)) *
            ratioExponential *
            ((tailCoefficientCubeAverage M L m ω)⁻¹ *
              (3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) +
          Kmean * (3 * Keps * lambda * (gap + 1)) *
              vectorSupNormOn (cube d (m : ℤ)) h.grad * boundaryTop +
          5 / 2 * Kboundary *
              (3 : ℝ) ^ (-(((m : ℝ) - ((m - 5 : ℕ) : ℝ)) / 2)) *
              ((3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad) * boundaryTop ≤
        3 * Kbudget * ((1 + lambda * gap) * ratioExponential) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            (forcing + outsideIndicator *
              fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
                (1 / 2) h.grad)) := by
    rw [htopReal]
    have hgapFive : ((m : ℝ) - ((m : ℝ) - 5)) / 2 = (5 / 2 : ℝ) := by ring
    rw [hgapFive]
    rw [← hAforceDef, ← hAboundDef]
    calc
      Aforce * ratioExponential *
              ((tailCoefficientCubeAverage M L m ω)⁻¹ *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) +
            Kmean * (3 * Keps * lambda * (gap + 1)) *
                vectorSupNormOn (cube d (m : ℤ)) h.grad * boundaryTop +
            Abound * ((3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad) * boundaryTop =
          Aforce * ratioExponential * ((3 : ℝ) ^ ((m : ℝ) / 2) * forcing) +
            Amean * lambda * (gap + 1) *
              (vectorSupNormOn (cube d (m : ℤ)) h.grad * boundaryTop) +
            Abound * ((3 : ℝ) ^ ((m : ℝ) / 2) *
              (holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad *
                boundaryTop)) := by
            rw [hAmeanDef]
            dsimp only [forcing]
            ring
      _ ≤ _ := hbudget
  let Aexp : ℝ := Real.exp (Citer * ((k : ℝ) + 1) *
      ((k : ℝ) + 2 + lambda * gap) +
    Citer * (3 * Keps * lambda * (gap + 1)))
  let exponential : ℝ := (1 + lambda * gap) * ratioExponential
  refine ⟨Aexp, exponential, Real.exp_nonneg _, ?_, ?_, ?_⟩
  · dsimp only [exponential]
    have hlinear1 : 1 ≤ 1 + lambda * gap :=
      le_add_of_nonneg_right (mul_nonneg hlam0 hgap0)
    calc
      1 ≤ ratioExponential := hratio1
      _ ≤ (1 + lambda * gap) * ratioExponential := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hlinear1 (by positivity : 0 ≤ ratioExponential)
  ·
    have hstep := Section6HolderBoundary.expAbar_mul_linearRatio_le (Keps := Keps)
      (Cratio := ratioRate_cut d) (Cabs := Cabs) (gap := gap) (k := (k : ℝ))
      (Citer := Citer) (alpha := alpha) (C1 := C1) hCiter.le (ratioRate_nonneg_cut d)
      hgap0 (Nat.cast_nonneg k) halpha hC1pos
      (by
        intro a ha gp hgp
        rw [← hA0Def, ← hPDef]
        exact habsorbC1 a ha gp hgp)
    dsimp only [Aexp, exponential]
    rw [show lambda = C1⁻¹ * (1 - alpha) by
      dsimp only [lambda]; rw [Section6Stopping.holderStoppingLambda]]
    dsimp only [ratioExponential, gap, lambda]
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by norm_num) _)
  · have houtBudget :
        (3 : ℝ) ^ (-(ell : ℤ)) *
              normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
                (fun p => u.toFun p -
                  averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
          Aexp * ((3 : ℝ) ^ (-((m - 5 : ℕ) : ℤ)) *
                normalizedL2On (truncatedCube d (m : ℤ) ((m - 5 : ℕ) : ℤ) y)
                  (fun p => u.toFun p - averageOn
                    (truncatedCube d (m : ℤ) ((m - 5 : ℕ) : ℤ) y) u.toFun) +
              3 * Kbudget * exponential *
                ((3 : ℝ) ^ ((m : ℝ) / 2) *
                  (forcing + outsideIndicator *
                    fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
                      (1 / 2) h.grad))) := by
      dsimp only [Aexp, exponential]
      apply hout.trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact add_le_add (le_refl _) (by
        simpa only [gap, lambda, boundaryTop, ratioExponential] using hDbudget)
    rw [← rpow_neg_natCast_eq_zpow ell, ← rpow_neg_natCast_eq_zpow (m - 5),
      htopReal, htopCast] at houtBudget
    dsimp only [forcing] at houtBudget
    rw [tailCoefficientCubeAverage_eq_tailAverage_cube] at houtBudget
    dsimp only [outsideIndicator] at houtBudget
    rw [hKdataCoeff]
    by_cases hinterior : x ∈ cube d ((m : ℤ) - 1)
    · simpa only [if_pos hinterior, zero_mul, add_zero] using houtBudget
    · simpa only [if_neg hinterior, one_mul] using houtBudget

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderBelow
