import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneGate

/-!
# The gated Campanato estimate, applied at the manuscript's parameters

The deep-branch output of frozen row 1, in exactly the shape
`RowOneJoint.interiorRowOne_combinedJoint` consumes: the `hlong` inequality
together with the joint absorption bound `habs`.

The constant-selection chain is the forced one, and `P` carries the extra
`ratioRate d` summand so that the ladder exponential and the coefficient ratio
are absorbed together.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The deep-branch row-1 output.** -/
theorem exists_interiorCampanatoOutput (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ (C1 C2 Cabs Kforce : ℝ), 0 < C1 ∧ 1 ≤ C2 ∧ 1 ≤ Cabs ∧ 0 ≤ Kforce ∧
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
      ∀ L m : ℕ, m ≤ L →
      ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
          (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
      ∀ n : ℕ,
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) 0 m ω : ℤ) ≤
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
    exists_interiorHolderCampanatoFullGate d hExcess
  obtain ⟨k, C2, hk, hC2, hth⟩ :=
    Section6Holder.exists_holderContractionParameters d Cstep hCstep
  obtain ⟨hthetaIoo, hthetak, hcontract⟩ := hth
  set Keps : ℝ := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K with hKepsDef
  set Kforce : ℝ := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
    with hKforceDef
  have hKeps0 : 0 ≤ Keps := by rw [hKepsDef]; positivity
  have hKforce0 : 0 ≤ Kforce := by
    have := Section6ExcessDecay.fractionalHolderConst_nonneg d
    rw [hKforceDef]; positivity
  set A0 : ℝ := Citer * ((k : ℝ) + 1) * ((k : ℝ) + 2) with hA0Def
  set P : ℝ := Citer * ((k : ℝ) + 1) + 3 * Citer * Keps + ratioRate d with hPDef
  have hP0 : 0 ≤ P := by
    have := ratioRate_nonneg d
    rw [hPDef]; positivity
  obtain ⟨C1, Cabs, hC1, hCabs, habsorb⟩ :=
    Section6Holder.exists_holderExponentialAbsorption A0 P hP0
  refine ⟨C1, C2, max Cabs 1, Kforce, hC1, hC2, le_max_right _ _, hKforce0, ?_⟩
  intro M hsmall alpha halpha hepsIcc hdelta heps8 hlam0 hlam1 L m hmL ω u g
    hsol hg n hstop x hx ell hell hdeep y hygrid hy
  -- context
  have hycube : y ∈ cube d (m : ℤ) := rowOne_centre_mem hy
  have hnm5 : (n : ℤ) ≤ (m : ℤ) - 5 :=
    base_scale_le_of_stopping M alpha _ _ 0 m n ω hstop
  obtain ⟨htoplt, htople⟩ := rowOne_base_lt_top hnm5 hell hdeep
  have hgate := rowOne_gate hx hy hnm5 htople
  have hstopEll := rowOne_stopping_at_base M alpha _ _ 0 m n ell ω hstop hell
  obtain ⟨hctrlY, hctrl0⟩ :=
    stoppedControls_pair M C1 C2 alpha 0 m ell ω hstopEll y hygrid hycube
  have hepsPos : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha := by
    rw [Section6Stopping.holderStoppingEpsilon]
    have hC2pos : (0 : ℝ) < C2 := by linarith
    have : (0 : ℝ) ≤ Real.sqrt (1 - alpha) := Real.sqrt_nonneg _
    positivity
  have hratio := stoppedRatio_row (L := L) M C1 C2 alpha 0 m ell (m - 5) ω
    (by omega) hmL (by omega) hlam0 hlam1 hepsPos hdelta y hycube hstopEll hygrid
  -- the contraction hypothesis
  have hepsC2 : Section6Stopping.holderStoppingEpsilon C2 alpha ≤ C2⁻¹ := by
    rw [Section6Stopping.holderStoppingEpsilon]
    have hC2pos : (0 : ℝ) < C2 := by linarith
    have hsq : Real.sqrt (1 - alpha) ≤ 1 := by
      have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith [halpha.1]
      have := Real.sqrt_le_sqrt h1
      simpa using this
    have hinv : (0 : ℝ) ≤ C2⁻¹ := by positivity
    nlinarith [hsq, hinv]
  have hcontr := hcontract (Section6Stopping.holderStoppingEpsilon C2 alpha)
    hepsPos hepsC2
  -- apply the gated estimate
  have hout := hcamp M hsmall (Section6Stopping.holderStoppingEpsilon C2 alpha)
    hepsIcc (Section6Stopping.holderStoppingLambda C1 alpha) hlam0 hdelta heps8
    k hk ((3 : ℝ) ^ (-(1 / 4 : ℝ))) hthetaIoo hthetak hcontr
    L m ell (m - 5) htoplt htople hmL y hycube hgate ω hctrlY.1 hctrlY.2
    (Real.exp (ratioRate d * Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (ell : ℝ)))) (Real.exp_nonneg _) hratio u g hsol hg
  dsimp only at hout
  refine ⟨Real.exp (Citer * ((k : ℝ) + 1) *
      ((k : ℝ) + 2 + Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (ell : ℝ))) +
      Citer * (3 * Keps * Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (ell : ℝ) + 1))),
    Real.exp (ratioRate d * Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (ell : ℝ))),
    (Real.exp_nonneg _), ?_, ?_, ?_⟩
  · have hgap : (0 : ℝ) ≤ (m : ℝ) - (ell : ℝ) := by linarith only [hdeep]
    have hx0 : (0 : ℝ) ≤ ratioRate d *
        Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (ell : ℝ)) :=
      mul_nonneg (mul_nonneg (ratioRate_nonneg d) hlam0) hgap
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ _ := Real.exp_le_exp.mpr hx0
  · -- the joint absorption bound
    have hlamEq : Section6Stopping.holderStoppingLambda C1 alpha =
        C1⁻¹ * (1 - alpha) := by rw [Section6Stopping.holderStoppingLambda]
    rw [hlamEq]
    have hstep := expAbar_mul_ratio_le (Keps := Keps) (Cratio := ratioRate d)
      (Cabs := Cabs) (gap := (m : ℝ) - (ell : ℝ)) (k := (k : ℝ))
      (Citer := Citer) (alpha := alpha) (C₁ := C1) hCiter.le (ratioRate_nonneg d)
      (by linarith only [hdeep]) (Nat.cast_nonneg k) halpha hC1
      (by
        intro a ha gp hgp
        rw [← hA0Def, ← hPDef]
        exact habsorb a ha gp hgp)
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by norm_num) _)
  · -- the shape match
    rw [← hKepsDef, ← hKforceDef] at hout
    have hcast : ((m - 5 : ℕ) : ℤ) = (m : ℤ) - 5 := by omega
    rw [← hcast]
    exact campanatoOutput_to_hlong M L m ell (m - 5) ω g (by omega) hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
