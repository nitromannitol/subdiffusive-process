import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFamily
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationLegCompose
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoCollapse
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoDataPairing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.StoppingRowsRaised




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The family leg.** -/
theorem exists_interiorRowTwoFamilyLeg (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ (C2min A0 P Kf : ℝ), 1 ≤ C2min ∧ 0 ≤ A0 ∧ 0 ≤ P ∧ 0 ≤ Kf ∧
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
      ∀ step L m n gate K top : ℕ, m ≤ L →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ z x : Vec d, OnTriadicGrid n z → z ∈ cube d ((m : ℤ) - 1) →
        x ∈ cube d (m : ℤ) →
        (∀ i : Fin d, |x i - z i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n) →
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        n + 4 ≤ gate → gate ≤ n + 4 + K → n + 2 * K + 11 < m →
        gate + 1 < top → top + 5 ≤ m →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        ∃ Abar D : ℝ,
          Abar ≤ A0 + P * (Section6Stopping.holderStoppingLambda C1 alpha *
            ((m : ℝ) - (n : ℝ) + 1)) ∧
          (3 : ℝ) ^ (-(gate : ℤ)) *
              normalizedL2On (truncatedCube d (m : ℤ) (gate : ℤ) x)
                (fun p ↦ u.toFun p -
                  averageOn (truncatedCube d (m : ℤ) (gate : ℤ) x) u.toFun) ≤
            oscillationLegPrice d * (Real.exp Abar *
              ((3 : ℝ) ^ (-(top : ℤ)) *
                normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
                  (fun p ↦ u.toFun p -
                    averageOn (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun) +
                D)) ∧
          Real.sqrt (tailAverage M L (gate + 2) omega
              (translatedCube d ((gate : ℤ) + 2) z)) * D ≤
            5 / 2 * Kf * rowTwoRatioBound d C1 alpha m n *
                rowTwoRatioBound d C1 alpha m n *
              ((tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by
  classical
  obtain ⟨Cstep, Kbud, Citer, hCstep, hKbud, hCiter, hfam⟩ :=
    exists_interiorCampanatoFamily d hExcess
  obtain ⟨k, C2, hk, hC2, hth⟩ :=
    Section6Holder.exists_holderContractionParameters d Cstep hCstep
  obtain ⟨hthetaIoo, hthetak, hcontract⟩ := hth
  set Keps : ℝ := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * Kbud with hKepsDef
  set Kforce : ℝ := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
    with hKforceDef
  have hKeps0 : 0 ≤ Keps := by rw [hKepsDef]; positivity
  have hKforce0 : 0 ≤ Kforce := by
    have := Section6ExcessDecay.fractionalHolderConst_nonneg d
    rw [hKforceDef]; positivity
  refine ⟨C2, Citer * ((k : ℝ) + 1) * ((k : ℝ) + 2),
    2 * Citer * ((k : ℝ) + 1) + 6 * Citer * Keps, Kforce, hC2, ?_, ?_, hKforce0, ?_⟩
  · have := hCiter.le
    positivity
  · have := hCiter.le
    positivity
  intro C2' hC2ge M hsmall C1 alpha halpha hepsIcc hdelta heps8 hlam0 hlam1
    step L m n gate K top hmL omega z x hzgrid hz hx hdist hstop hngate hgateK
    hroomBig hgatetop htopm u g hsol hg
  have hnmN : n < m := by omega
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hz
  have hC2' : 1 ≤ C2' := le_trans hC2 hC2ge
  have heps0 : 0 ≤ Section6Stopping.holderStoppingEpsilon C2' alpha :=
    holderStoppingEpsilon_nonneg (by linarith)
  have hE0' : 0 ≤ rowTwoRatioBound d C1 alpha m n :=
    rowTwoRatioBound_nonneg d C1 alpha m n
  obtain ⟨hctrlZ, _⟩ := stoppedControls_pair M C1 C2' alpha step m n omega hstop
    z hzgrid hzm
  have hgateRle : ((gate + 1 : ℕ) : ℝ) ≤ (n : ℝ) + (K : ℝ) + 5 := by
    have h : (gate + 1 : ℕ) ≤ n + K + 5 := by omega
    exact_mod_cast h
  have hnGate : (n : ℝ) ≤ ((gate + 1 : ℕ) : ℝ) := by
    have h : n ≤ gate + 1 := by omega
    exact_mod_cast h
  have hGatem : ((gate + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
    have h : gate + 1 ≤ m := by omega
    exact_mod_cast h
  have hKgap : 2 * ((K : ℝ) + 5) ≤ (m : ℝ) - (n : ℝ) := by
    have h : (n : ℝ) + 2 * (K : ℝ) + 11 ≤ (m : ℝ) := by
      have h' : n + 2 * K + 11 ≤ m := by omega
      exact_mod_cast h'
    linarith
  have hinfl : Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ)) ≤
      (2 * Section6Stopping.holderStoppingLambda C1 alpha) *
        ((m : ℝ) - ((gate + 1 : ℕ) : ℝ)) := by
    refine stopping_inflation_of_gap hlam0 (by omega) ?_
    linarith
  have hratio := stoppedRatio_row (L := L) M C1 C2' alpha step m n top omega
    hnmN hmL htopm hlam0 hlam1 heps0 hdelta z hzm hstop hzgrid
  have hfamZ := hfam M hsmall (Section6Stopping.holderStoppingEpsilon C2' alpha)
    hepsIcc (Section6Stopping.holderStoppingLambda C1 alpha)
    (2 * Section6Stopping.holderStoppingLambda C1 alpha) (by linarith)
    (by linarith) (by linarith)
    k hk ((3 : ℝ) ^ (-(1 / 4 : ℝ))) hthetaIoo hthetak
    (hcontract (Section6Stopping.holderStoppingEpsilon C2' alpha) heps0
      (by
        rw [Section6Stopping.holderStoppingEpsilon]
        have hC2pos : (0 : ℝ) < C2 := by linarith
        have hC2'pos : (0 : ℝ) < C2' := by linarith
        have hsq : Real.sqrt (1 - alpha) ≤ 1 := by
          have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith [halpha.1]
          have h2 := Real.sqrt_le_sqrt h1
          simpa using h2
        have hinv : (0 : ℝ) ≤ C2'⁻¹ := by positivity
        have hmono : C2'⁻¹ ≤ C2⁻¹ := inv_anti₀ hC2pos hC2ge
        calc C2'⁻¹ * Real.sqrt (1 - alpha) ≤ C2'⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left hsq hinv
          _ = C2'⁻¹ := by ring
          _ ≤ C2⁻¹ := hmono))
    L m n (gate + 1) top (by omega) (by omega) (by omega) hmL z hz omega
    hctrlZ.1 hctrlZ.2 hinfl (rowTwoRatioBound d C1 alpha m n) hE0'
    (fun j hj => by
      refine hratio j ?_
      rw [Finset.mem_Icc] at hj ⊢
      omega)
    u g hsol hg
  dsimp only at hfamZ
  rw [show ((gate + 1 : ℕ) : ℤ) = (gate : ℤ) + 1 from by push_cast; ring,
    ← hKepsDef, ← hKforceDef] at hfamZ
  -- the off-grid transfer to the grid centre
  have hsub : truncatedCube d (m : ℤ) (gate : ℤ) x ⊆
      truncatedCube d (m : ℤ) ((gate : ℤ) + 1) z := by
    refine truncatedCube_subset_of_dist ?_
    intro i
    refine (hdist i).trans ?_
    have hle : (3 : ℝ) ^ (n : ℤ) ≤ (3 : ℝ) ^ (gate : ℤ) := by
      refine zpow_le_zpow_right₀ (by norm_num) ?_
      omega
    have hpow : (3 : ℝ) ^ (n : ℕ) = (3 : ℝ) ^ (n : ℤ) := by rw [zpow_natCast]
    have h3 : (3 : ℝ) ^ ((gate : ℤ) + 1) = 3 * (3 : ℝ) ^ (gate : ℤ) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; ring
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (gate : ℤ) := zpow_pos (by norm_num) _
    rw [hpow, h3]
    linarith
  have htrans := normalizedL2On_sub_average_crossCentre_le (d := d) (m := (m : ℤ))
    (j := (gate : ℤ)) (ell := (gate : ℤ) + 1) hx hzm (by omega) (by omega) hsub u
  rw [show (gate : ℤ) + 1 - (gate : ℤ) + 2 = (3 : ℤ) from by ring] at htrans
  have hcompose := oscillationLeg_compose (j := (gate : ℤ)) (top := (top : ℤ))
    htrans hfamZ (Real.sqrt_nonneg _)
  rw [show (3 : ℝ) * Real.sqrt (((3 : ℝ) ^ (3 : ℤ)) ^ d) = oscillationLegPrice d
    from rfl] at hcompose
  -- the defect budget against the frozen datum
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
  have hStf := rowTwo_data_pairing M C1 C2' alpha step m n (gate + 2) L omega z
    hzgrid hzm hstop hnmN (by omega) (by omega) hmL hlam0 hlam1 heps0 hdelta g hg
  rw [show ((gate + 2 : ℕ) : ℤ) = (gate : ℤ) + 2 from by push_cast; ring] at hStf
  have ht1 : (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have h : (top : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : top ≤ m)
    simp only [neg_nonpos]
    linarith
  have ht0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) :=
    Real.rpow_nonneg (by norm_num) _
  refine ⟨_, _, ?_, hcompose, rowTwo_defect_arith hKforce0 hE0' ht0 ht1 hDa0 hStf⟩
  have hc1 : (0 : ℝ) ≤ 2 * Citer * ((k : ℝ) + 1) := by
    have := hCiter.le
    positivity
  have hc2 : (0 : ℝ) ≤ 6 * Citer * Keps := by
    have := hCiter.le
    positivity
  have e1 : Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - ((gate + 1 : ℕ) : ℝ)) ≤
      Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam0
  have e2 : Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1) ≤
      Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam0
  nlinarith only [mul_le_mul_of_nonneg_left e1 hc1,
    mul_le_mul_of_nonneg_left e2 hc2]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
