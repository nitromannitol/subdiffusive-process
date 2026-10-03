module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneOutputStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoAbsorb
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.CampanatoFullGate
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.ExcessDecayInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowOneInstantiation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.StoppingWindows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.ContractionParameters

@[expose] public section

/-!
# The gated Campanato estimate with **free** stopping parameters

`RowOneOutputStep.exists_interiorCampanatoOutputAtStep` returns the pair
`(C₁, C₂)` of stopping parameters *pinned*: `C₁` is whatever
`Section6Holder.exists_holderExponentialAbsorption` produced and `C₂` whatever
`Section6Holder.exists_holderContractionParameters` produced, with no relation
between them.  The three frozen rows must run at **one** stopping scale, so the
row packages need a single admissible `(C₁, C₂)`; that is impossible while each
row pins its own.

This module re-runs the output with both parameters universally quantified above
their thresholds.  Nothing in the proof changes except two monotonicity steps:

* the absorption survives enlarging `C₁`
  (`RowTwoAbsorb.holderExponentialAbsorption_mono`: the exponent decreases and
  the right-hand side does not depend on `C₁`);
* the contraction clause is `∀ eps, 0 ≤ eps → eps ≤ C₂ₘᵢₙ⁻¹ → …` and enlarging
  `C₂` only shrinks `epsilon = C₂⁻¹√(1-alpha)`, so the raise is free
  (`inv_anti₀`), exactly as in `RowTwoFamilyLeg`.

The deterministic margin `step` is also universally quantified, since none of
the constants depends on it.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The deep-branch row-1 output, at any admissible stopping parameters.** -/
theorem exists_interiorCampanatoOutputAtStepFree_cut (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput_cut d) :
    ∃ (C1min C2min Cabs Kforce : ℝ), 1 ≤ C1min ∧ 1 ≤ C2min ∧ 1 ≤ Cabs ∧
      0 ≤ Kforce ∧
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
      ∀ L m : ℕ, ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
          (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
      ∀ n : ℕ,
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
      ∀ x : Vec d, x ∈ cube d ((m : ℤ) - 1) →
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
              5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
                ((3 : ℝ) ^ ((m : ℝ) / 2) *
                  ((tailAverage M L m ω (cube d (m : ℤ)))⁻¹ *
                    holderSeminormOn (cube d (m : ℤ)) (1 / 2) g))) := by
  classical
  obtain ⟨Cstep, K, Citer, hCstep, hK, hCiter, hcamp⟩ :=
    exists_interiorHolderCampanatoFullGate_cut d hExcess
  obtain ⟨k, C2min, hk, hC2min, hth⟩ :=
    RowsHolder.exists_holderContractionParameters_cut d Cstep hCstep
  obtain ⟨hthetaIoo, hthetak, hcontract⟩ := hth
  set Keps : ℝ := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-2 : ℝ) * K with hKepsDef
  set Kforce : ℝ := Cstep * (1 / 4 : ℝ) ^ (-8 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
    with hKforceDef
  have hKeps0 : 0 ≤ Keps := by rw [hKepsDef]; positivity
  have hKforce0 : 0 ≤ Kforce := by
    have := Section6ExcessDecay.fractionalHolderConst_nonneg d
    rw [hKforceDef]; positivity
  set A0 : ℝ := Citer * ((k : ℝ) + 1) * ((k : ℝ) + 2) with hA0Def
  set P : ℝ := Citer * ((k : ℝ) + 1) + 3 * Citer * Keps + ratioRate_cut d with hPDef
  have hP0 : 0 ≤ P := by
    have := ratioRate_nonneg_cut d
    rw [hPDef]; positivity
  obtain ⟨C1abs, Cabs, hC1abs, hCabs, habsorb⟩ :=
    Section6Holder.exists_holderExponentialAbsorption A0 P hP0
  refine ⟨max C1abs 1, C2min, max Cabs 1, Kforce, le_max_right _ _, hC2min,
    le_max_right _ _, hKforce0, ?_⟩
  intro C1 C2 hC1thr hC2ge step M hsmall alpha halpha hepsIcc hdelta heps8
    hlam0 hlam1 L m ω u g hsol hg n hstop x hx ell hell hdeep y hygrid hy
  have hC1pos : (0 : ℝ) < C1 := lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_right C1abs 1) hC1thr)
  have hC2 : (1 : ℝ) ≤ C2 := le_trans hC2min hC2ge
  -- the absorption at the enlarged `C₁`
  have habsorbC1 := holderExponentialAbsorption_mono hP0 hC1abs
    (le_trans (le_max_left C1abs 1) hC1thr) habsorb
  -- context
  have hycube : y ∈ cube d (m : ℤ) := rowOne_centre_mem hy
  have hnm5 : (n : ℤ) ≤ (m : ℤ) - 5 :=
    base_scale_le_of_stopping_cut M alpha _ _ step m n ω hstop
  obtain ⟨htoplt, htople⟩ := rowOne_base_lt_top hnm5 hell hdeep
  have hgate := rowOne_gate hx hy hnm5 htople
  have hstopEll := rowOne_stopping_at_base_cut M alpha _ _ step m n ell ω hstop hell
  obtain ⟨hctrlY, hctrl0⟩ :=
    stoppedControls_pair_cut M C1 C2 alpha step m ell ω hstopEll y hygrid hycube
  have hepsPos : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha := by
    rw [Section6Stopping.holderStoppingEpsilon]
    have hC2pos : (0 : ℝ) < C2 := by linarith
    have : (0 : ℝ) ≤ Real.sqrt (1 - alpha) := Real.sqrt_nonneg _
    positivity
  have hratio := stoppedRatio_row_cut (L := L) M C1 C2 alpha step m ell (m - 5) ω
    (by omega) (by omega) hlam0 hlam1 hepsPos hdelta y hycube hstopEll hygrid
  -- the contraction hypothesis, at the raised `C₂`
  have hepsC2 : Section6Stopping.holderStoppingEpsilon C2 alpha ≤ C2min⁻¹ := by
    rw [Section6Stopping.holderStoppingEpsilon]
    have hC2minpos : (0 : ℝ) < C2min := by linarith
    have hC2pos : (0 : ℝ) < C2 := by linarith
    have hsq : Real.sqrt (1 - alpha) ≤ 1 := by
      have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith [halpha.1]
      have := Real.sqrt_le_sqrt h1
      simpa using this
    have hinv : (0 : ℝ) ≤ C2⁻¹ := by positivity
    have hmono : C2⁻¹ ≤ C2min⁻¹ := inv_anti₀ hC2minpos hC2ge
    calc C2⁻¹ * Real.sqrt (1 - alpha) ≤ C2⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hsq hinv
      _ = C2⁻¹ := by ring
      _ ≤ C2min⁻¹ := hmono
  have hcontr := hcontract (Section6Stopping.holderStoppingEpsilon C2 alpha)
    hepsPos hepsC2
  -- apply the gated estimate
  have hout := hcamp M hsmall (Section6Stopping.holderStoppingEpsilon C2 alpha)
    hepsIcc (Section6Stopping.holderStoppingLambda C1 alpha) hlam0 hdelta heps8
    k hk ((3 : ℝ) ^ (-(1 / 4 : ℝ))) hthetaIoo hthetak hcontr
    L m ell (m - 5) htoplt htople y hycube hgate ω hctrlY.1 hctrlY.2
    (Real.exp (ratioRate_cut d * Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (ell : ℝ)))) (Real.exp_nonneg _) hratio u g hsol hg
  dsimp only at hout
  refine ⟨Real.exp (Citer * ((k : ℝ) + 1) *
      ((k : ℝ) + 2 + Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (ell : ℝ))) +
      Citer * (3 * Keps * Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (ell : ℝ) + 1))),
    Real.exp (ratioRate_cut d * Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (ell : ℝ))),
    (Real.exp_nonneg _), ?_, ?_, ?_⟩
  · have hgap : (0 : ℝ) ≤ (m : ℝ) - (ell : ℝ) := by linarith only [hdeep]
    have hx0 : (0 : ℝ) ≤ ratioRate_cut d *
        Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (ell : ℝ)) :=
      mul_nonneg (mul_nonneg (ratioRate_nonneg_cut d) hlam0) hgap
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ _ := Real.exp_le_exp.mpr hx0
  · -- the joint absorption bound
    have hlamEq : Section6Stopping.holderStoppingLambda C1 alpha =
        C1⁻¹ * (1 - alpha) := by rw [Section6Stopping.holderStoppingLambda]
    rw [hlamEq]
    have hstep := expAbar_mul_ratio_le (Keps := Keps) (Cratio := ratioRate_cut d)
      (Cabs := Cabs) (gap := (m : ℝ) - (ell : ℝ)) (k := (k : ℝ))
      (Citer := Citer) (alpha := alpha) (C₁ := C1) hCiter.le (ratioRate_nonneg_cut d)
      (by linarith only [hdeep]) (Nat.cast_nonneg k) halpha hC1pos
      (by
        intro a ha gp hgp
        rw [← hA0Def, ← hPDef]
        exact habsorbC1 a ha gp hgp)
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by norm_num) _)
  · -- the shape match
    rw [← hKepsDef, ← hKforceDef] at hout
    have hcast : ((m - 5 : ℕ) : ℤ) = (m : ℤ) - 5 := by omega
    rw [← hcast]
    exact campanatoOutput_to_hlong M L m ell (m - 5) ω g (by omega) hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
