module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoFamilyLeg
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoFamilyLeg
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoTopLegAt
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoTopLegAt
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.ExcessDecayInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.GateParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowOneInstantiation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoRatioScales

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **Row 2's oscillation leg.** -/
theorem exists_interiorRowTwoOscLeg_cut (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput_cut d) :
    ∃ (C2min A0 P Kpre : ℝ), 1 ≤ C2min ∧ 0 ≤ A0 ∧ 0 ≤ P ∧ 0 ≤ Kpre ∧
      ∀ C2 : ℝ, C2min ≤ C2 →
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ C1 alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤
          Section6Stopping.holderStoppingLambda C1 alpha →
        0 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
      ∀ step L m n gate K : ℕ, ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ z x : Vec d, OnTriadicGrid n z → z ∈ cube d ((m : ℤ) - 1) →
        x ∈ cube d (m : ℤ) →
        (∀ i : Fin d, |x i - z i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n) →
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        n + 4 ≤ gate → gate ≤ n + 4 + K →
        (K : ℝ) ≤ Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) + 1 →
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1 →
        n + 2 * K + 11 < m →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        Real.sqrt (tailAverage M L (gate + 2) omega
            (translatedCube d ((gate : ℤ) + 2) z)) *
            ((3 : ℝ) ^ (-(gate : ℤ)) *
              normalizedL2On (truncatedCube d (m : ℤ) (gate : ℤ) x)
                (fun p ↦ u.toFun p -
                  averageOn (truncatedCube d (m : ℤ) (gate : ℤ) x) u.toFun)) ≤
          Kpre * Real.exp (A0 + P *
              (Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ) + 1))) *
            (vectorNormalizedL2On (cube d (m : ℤ))
                (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
                  u.grad p) +
              (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by
  classical
  obtain ⟨C2, A0f, Pf, Kf, hC2, hA0f, hPf, hKf, hfamLeg⟩ :=
    exists_interiorRowTwoFamilyLeg_cut d hExcess
  obtain ⟨Kosc, hKosc0, htopleg⟩ := exists_interiorRowTwoTopLegAt_cut d
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hr0 : (0 : ℝ) ≤ ratioRate_cut d := ratioRate_nonneg_cut d
  have hdlog0 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by positivity
  refine ⟨C2, A0f + 8 * (d : ℝ) * Real.log 3,
    Pf + 2 * ratioRate_cut d + (d : ℝ) * Real.log 3,
    oscillationLegPrice d * (Kosc + 5 / 2 * Kf), hC2, by linarith, by linarith,
    mul_nonneg (oscillationLegPrice_nonneg d) (by linarith), ?_⟩
  intro C2' hC2ge M hsmall C1 alpha halpha hepsIcc hdelta heps8 hlam0 hlam1
    step L m n gate K omega z x hzgrid hz hx hdist hstop hngate hgateK hKub
    hroom hroomBig u g hsol hg
  have hC2' : 1 ≤ C2' := le_trans hC2 hC2ge
  have hnmN : n < m := by omega
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hz
  have heps0 : 0 ≤ Section6Stopping.holderStoppingEpsilon C2' alpha :=
    holderStoppingEpsilon_nonneg_cut (by linarith)
  have heps1 : Section6Stopping.holderStoppingEpsilon C2' alpha ≤ 1 :=
    holderStoppingEpsilon_le_one_cut hC2' halpha.1
  have hE0' : 0 ≤ rowTwoRatioBound_cut d C1 alpha m n :=
    rowTwoRatioBound_nonneg_cut d C1 alpha m n
  have hgapR0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_of_lt hnmN)
    linarith
  have hw0 : (0 : ℝ) ≤ Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (n : ℝ) + 1) := by positivity
  have hlamgap : Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ)) ≤
      Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam0
  -- the selected top scale
  obtain ⟨top, hntop, htopm, hmtop, htop⟩ := htopleg M hsmall C1 C2' alpha heps0
    heps1 hlam0 hlam1 hdelta step L m n K (gate + 2) omega z hzgrid hz hstop
    (by omega) hroom hnmN (by omega) (by omega) u
  rw [show ((gate + 2 : ℕ) : ℤ) = (gate : ℤ) + 2 from by push_cast; ring] at htop
  -- the family leg at that top
  obtain ⟨Abar, D, hAbar, hcompose, hD⟩ := hfamLeg C2' hC2ge M hsmall C1 alpha halpha
    hepsIcc hdelta heps8 hlam0 hlam1 step L m n gate K top omega z x hzgrid
    hz hx hdist hstop hngate hgateK hroomBig (by omega) htopm u g hsol hg
  -- the two legs, combined
  have hEg0 : 0 ≤ vectorNormalizedL2On (cube d (m : ℤ))
      (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p) :=
    Real.sqrt_nonneg _
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hbeq : tailCoefficientCubeAverage M L m omega =
      tailAverage M L m omega (cube d (m : ℤ)) :=
    tailCoefficientCubeAverage_eq_tailAverage_cube M L m omega
  have hDa0 : 0 ≤ (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
      (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d (m : ℤ)) (1 / 2) g := by
    have h1 : (0 : ℝ) ≤ (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) :=
      Real.rpow_nonneg (by rw [← hbeq]; exact hb.le) _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have h3 : 0 ≤ holderSeminormOn (cube d (m : ℤ)) (1 / 2) g :=
      Section6ExcessDecay.holderSeminormOn_nonneg hg
    positivity
  have hKtop0 : 0 ≤ rowTwoRatioBound_cut d C1 alpha m n *
      (Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ))) :=
    mul_nonneg hE0' (mul_nonneg hKosc0 (scaleTransferPrice_nonneg d _))
  have hKdat0 : (0 : ℝ) ≤ 5 / 2 * Kf * rowTwoRatioBound_cut d C1 alpha m n *
      rowTwoRatioBound_cut d C1 alpha m n :=
    mul_nonneg (mul_nonneg (by linarith) hE0') hE0'
  have harith := rowTwo_oscLeg_arith (oscillationLegPrice_nonneg d)
    (Real.exp_nonneg _) (Real.sqrt_nonneg _) hcompose htop hD hKtop0 hKdat0
    hEg0 hDa0
  refine harith.trans ?_
  -- the exponential collapse
  have hEbound : rowTwoRatioBound_cut d C1 alpha m n ≤
      Real.exp (ratioRate_cut d * (Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ) + 1))) := by
    rw [rowTwoRatioBound_cut]
    refine Real.exp_le_exp.mpr ?_
    calc ratioRate_cut d * Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ))
        = ratioRate_cut d * (Section6Stopping.holderStoppingLambda C1 alpha *
            ((m : ℝ) - (n : ℝ))) := by ring
      _ ≤ ratioRate_cut d * (Section6Stopping.holderStoppingLambda C1 alpha *
            ((m : ℝ) - (n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hlamgap hr0
  have hKw : (K : ℝ) ≤ Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (n : ℝ) + 1) + 1 := by linarith
  have hTPbound : scaleTransferPrice d ((m : ℤ) - (top : ℤ)) ≤
      Real.exp (8 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) *
        (Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ) + 1))) := by
    refine scaleTransferPrice_le_exp d (by omega) ?_
    rw [show (((m : ℤ) - (top : ℤ) : ℤ) : ℝ) = (m : ℝ) - (top : ℝ)
      from by push_cast; ring]
    have hmt : (m : ℝ) - (top : ℝ) ≤ (K : ℝ) + 5 := by
      have h : (m : ℝ) ≤ (top : ℝ) + (K : ℝ) + 5 := by exact_mod_cast hmtop
      linarith
    have hbase : (m : ℝ) - (top : ℝ) + 2 ≤
        Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ) + 1) + 8 := by linarith
    calc ((m : ℝ) - (top : ℝ) + 2) * (d : ℝ) * Real.log 3
        = ((m : ℝ) - (top : ℝ) + 2) * ((d : ℝ) * Real.log 3) := by ring
      _ ≤ (Section6Stopping.holderStoppingLambda C1 alpha *
            ((m : ℝ) - (n : ℝ) + 1) + 8) * ((d : ℝ) * Real.log 3) :=
          mul_le_mul_of_nonneg_right hbase hdlog0
      _ = 8 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) *
            (Section6Stopping.holderStoppingLambda C1 alpha *
              ((m : ℝ) - (n : ℝ) + 1)) := by ring
  refine rowTwo_collapse_arith
    (a1 := A0f + Pf * (Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (n : ℝ) + 1)))
    (a2 := 8 * (d : ℝ) * Real.log 3 +
      (2 * ratioRate_cut d + (d : ℝ) * Real.log 3) *
        (Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ) + 1)))
    (oscillationLegPrice_nonneg d) (add_nonneg hEg0 hDa0)
    (add_nonneg hKtop0 hKdat0) (Real.exp_le_exp.mpr hAbar) ?_ (by ring)
  refine rowTwo_Ksum_arith hKosc0 hKf ?_ ?_
  · refine (mul_le_exp_add (scaleTransferPrice_nonneg d _) hEbound hTPbound).trans ?_
    refine Real.exp_le_exp.mpr ?_
    nlinarith only [hr0, hw0, hdlog0]
  · refine (mul_le_exp_add hE0' hEbound hEbound).trans ?_
    refine Real.exp_le_exp.mpr ?_
    nlinarith only [hr0, hw0, hdlog0]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
