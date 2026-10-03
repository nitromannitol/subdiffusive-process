module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffCampanatoFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffDataPairing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffDataLegs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowOneInstantiation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationLegCompose
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.StoppingRowsRaised

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

noncomputable section
attribute [local instance] Classical.propDecidable

theorem aux_dedup_d049_boundaryDefectBudget_bound
    {S Kforce Kmean Keps Kboundary R w DataG DataH I F MeanTerm BoundaryTerm E : ℝ}
    (hKforce : 0 ≤ Kforce) (hKmean : 0 ≤ Kmean) (hKeps : 0 ≤ Keps)
    (hKboundary : 0 ≤ Kboundary) (hR0 : 0 ≤ R) (hR1 : 1 ≤ R)
    (hw : 0 ≤ w) (hDataG : 0 ≤ DataG) (hDataH : 0 ≤ DataH)
    (hI0 : 0 ≤ I) (hI1 : I ≤ 1)
    (hS0 : 0 ≤ S) (hF0 : 0 ≤ F) (hMean0 : 0 ≤ MeanTerm)
    (hBoundary0 : 0 ≤ BoundaryTerm)
    (hE : E ≤ 6 * Keps * w)
    (hF : S * F ≤ R * DataG)
    (hM : S * MeanTerm ≤ R * DataH)
    (hB : S * BoundaryTerm ≤ R * DataH) :
    S * (5 / 2 * Kforce * R * F + Kmean * E * MeanTerm * I +
        5 / 2 * Kboundary * BoundaryTerm * I) ≤
      (5 / 2 * Kforce + 6 * Kmean * Keps + 5 / 2 * Kboundary) *
        (1 + w) * R ^ 2 * (DataG + DataH) := by
  let Q : ℝ := (1 + w) * R ^ 2 * (DataG + DataH)
  have hone : (1 : ℝ) ≤ 1 + w := by linarith
  have hsum0 : 0 ≤ DataG + DataH := add_nonneg hDataG hDataH
  have hRG : R ^ 2 * DataG ≤ Q := by
    dsimp only [Q]
    have hsum : DataG ≤ DataG + DataH := by linarith
    calc
      R ^ 2 * DataG ≤ R ^ 2 * (DataG + DataH) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg R)
      _ = 1 * (R ^ 2 * (DataG + DataH)) := by ring
      _ ≤ (1 + w) * (R ^ 2 * (DataG + DataH)) :=
        mul_le_mul_of_nonneg_right hone (mul_nonneg (sq_nonneg R) hsum0)
      _ = (1 + w) * R ^ 2 * (DataG + DataH) := by ring
  have hRle : R ≤ R ^ 2 := by nlinarith
  have hsumH : DataH ≤ DataG + DataH := by linarith
  have hRM : w * I * R * DataH ≤ Q := by
    dsimp only [Q]
    calc
      w * I * R * DataH ≤ w * 1 * R ^ 2 * (DataG + DataH) := by gcongr
      _ ≤ (1 + w) * R ^ 2 * (DataG + DataH) := by
        have hrest : 0 ≤ R ^ 2 * (DataG + DataH) := by positivity
        calc
          w * 1 * R ^ 2 * (DataG + DataH) = w * (R ^ 2 * (DataG + DataH)) := by ring
          _ ≤ (1 + w) * (R ^ 2 * (DataG + DataH)) :=
            mul_le_mul_of_nonneg_right (by linarith) hrest
          _ = _ := by ring
  have hRB : I * R * DataH ≤ Q := by
    dsimp only [Q]
    calc
      I * R * DataH ≤ 1 * R ^ 2 * (DataG + DataH) := by gcongr
      _ = 1 * (R ^ 2 * (DataG + DataH)) := by ring
      _ ≤ (1 + w) * (R ^ 2 * (DataG + DataH)) :=
        mul_le_mul_of_nonneg_right hone (mul_nonneg (sq_nonneg R) hsum0)
      _ = (1 + w) * R ^ 2 * (DataG + DataH) := by ring
  have hSF0 : 0 ≤ S * F := mul_nonneg hS0 hF0
  have hSM0 : 0 ≤ S * MeanTerm := mul_nonneg hS0 hMean0
  have hSB0 : 0 ≤ S * BoundaryTerm := mul_nonneg hS0 hBoundary0
  calc
    S * (5 / 2 * Kforce * R * F + Kmean * E * MeanTerm * I +
        5 / 2 * Kboundary * BoundaryTerm * I) =
      5 / 2 * Kforce * R * (S * F) +
        Kmean * E * I * (S * MeanTerm) +
        5 / 2 * Kboundary * I * (S * BoundaryTerm) := by ring
    _ ≤ 5 / 2 * Kforce * R * (R * DataG) +
        Kmean * (6 * Keps * w) * I * (R * DataH) +
        5 / 2 * Kboundary * I * (R * DataH) := by gcongr
    _ = 5 / 2 * Kforce * (R ^ 2 * DataG) +
        6 * Kmean * Keps * (w * I * R * DataH) +
        5 / 2 * Kboundary * (I * R * DataH) := by ring
    _ ≤ 5 / 2 * Kforce * Q + 6 * Kmean * Keps * Q +
        5 / 2 * Kboundary * Q := by gcongr
    _ = (5 / 2 * Kforce + 6 * Kmean * Keps + 5 / 2 * Kboundary) * Q := by ring
    _ = _ := by ring

private theorem boundaryDefectBudget_bound
    {S Kforce Kmean Keps Kboundary R w DataG DataH I F MeanTerm BoundaryTerm E : ℝ}
    (hKforce : 0 ≤ Kforce) (hKmean : 0 ≤ Kmean) (hKeps : 0 ≤ Keps)
    (hKboundary : 0 ≤ Kboundary) (hR0 : 0 ≤ R) (hR1 : 1 ≤ R)
    (hw : 0 ≤ w) (hDataG : 0 ≤ DataG) (hDataH : 0 ≤ DataH)
    (hI0 : 0 ≤ I) (hI1 : I ≤ 1)
    (hS0 : 0 ≤ S) (hF0 : 0 ≤ F) (hMean0 : 0 ≤ MeanTerm)
    (hBoundary0 : 0 ≤ BoundaryTerm)
    (hE : E ≤ 6 * Keps * w)
    (hF : S * F ≤ R * DataG)
    (hM : S * MeanTerm ≤ R * DataH)
    (hB : S * BoundaryTerm ≤ R * DataH) :
    S * (5 / 2 * Kforce * R * F + Kmean * E * MeanTerm * I +
        5 / 2 * Kboundary * BoundaryTerm * I) ≤
      (5 / 2 * Kforce + 6 * Kmean * Keps + 5 / 2 * Kboundary) *
        (1 + w) * R ^ 2 * (DataG + DataH) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.aux_dedup_d049_boundaryDefectBudget_bound (S := S) (Kforce := Kforce) (Kmean := Kmean) (Keps := Keps) (Kboundary := Kboundary) (R := R) (w := w) (DataG := DataG) (DataH := DataH) (I := I) (F := F) (MeanTerm := MeanTerm) (BoundaryTerm := BoundaryTerm) (E := E) (hKforce := hKforce) (hKmean := hKmean) (hKeps := hKeps) (hKboundary := hKboundary) (hR0 := hR0) (hR1 := hR1) (hw := hw) (hDataG := hDataG) (hDataH := hDataH) (hI0 := hI0) (hI1 := hI1) (hS0 := hS0) (hF0 := hF0) (hMean0 := hMean0) (hBoundary0 := hBoundary0) (hE := hE) (hF := hF) (hM := hM) (hB := hB)

/-- The boundary Campanato family at the selected gate scale, including both
datum-gradient contributions. -/
theorem exists_boundaryRowTwoCutoffFamilyLeg (d : ℕ) [NeZero d]
    (hExcess : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
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
      ∀ step L m n gate K top : ℕ,
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ z x : Vec d, OnTriadicGrid n z → z ∈ cube d (m : ℤ) →
        x ∈ cube d (m : ℤ) →
        (∀ i : Fin d, |x i - z i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n) →
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        n + 4 ≤ gate → gate ≤ n + 4 + K → n + 2 * K + 11 < m →
        gate + 1 < top → top + 5 ≤ m →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
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
                    averageOn (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun) + D)) ∧
          Real.sqrt (tailAverage M L (gate + 2) omega
              (translatedCube d ((gate : ℤ) + 2) z)) * D ≤
            Kf * (1 + Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ) + 1)) *
              rowTwoRatioBound_cut d C1 alpha m n ^ 2 *
              ((tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  holderSeminormOn (cube d (m : ℤ)) (1 / 2) g +
                (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
                    (1 / 2) h.grad) := by
  classical
  obtain ⟨Cstep, Kbud, Citer, hCstep, hKbud, hCiter, hfam⟩ :=
    exists_boundaryRowTwoCutoffCampanatoFamily d hExcess
  obtain ⟨k, C2, hk, hC2, hthetaIoo, hthetak, hcontract⟩ :=
    Section6Holder.exists_holderContractionParameters d Cstep hCstep
  set Keps : ℝ := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * Kbud with hKepsDef
  set Kforce : ℝ := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
    with hKforceDef
  set Kmean : ℝ := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) with hKmeanDef
  set Kboundary : ℝ := Cstep * (1 / 4 : ℝ) ^ (-3 : ℤ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) with hKboundaryDef
  have hKeps0 : 0 ≤ Keps := by rw [hKepsDef]; positivity
  have hKforce0 : 0 ≤ Kforce := by
    rw [hKforceDef]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hCstep.le (Real.rpow_nonneg (by norm_num) _))
          (Real.rpow_nonneg (by norm_num) _))
        (Section6ExcessDecay.fractionalHolderConst_nonneg d))
      (Real.sqrt_nonneg _)
  have hKmean0 : 0 ≤ Kmean := by rw [hKmeanDef]; positivity
  have hKboundary0 : 0 ≤ Kboundary := by rw [hKboundaryDef]; positivity
  refine ⟨C2, Citer * ((k : ℝ) + 1) * ((k : ℝ) + 2),
    2 * Citer * ((k : ℝ) + 1) + 6 * Citer * Keps,
    5 / 2 * Kforce + 6 * Kmean * Keps + 5 / 2 * Kboundary,
    hC2, ?_, ?_, by positivity, ?_⟩
  · positivity
  · positivity
  intro C2' hC2ge M hsmall C1 alpha halpha hepsIcc hdelta heps8 hlam0 hlam1
    step L m n gate K top omega z x hzgrid hz hx hdist hstop hngate hgateK
    hroomBig hgatetop htopm u h g hsol hg hh
  have hnmN : n < m := by omega
  have hC2' : 1 ≤ C2' := le_trans hC2 hC2ge
  have heps0 : 0 ≤ Section6Stopping.holderStoppingEpsilon C2' alpha :=
    holderStoppingEpsilon_nonneg (by linarith)
  have hR0 : 0 ≤ rowTwoRatioBound_cut d C1 alpha m n :=
    rowTwoRatioBound_nonneg_cut d C1 alpha m n
  have hR1 : 1 ≤ rowTwoRatioBound_cut d C1 alpha m n :=
    one_le_rowTwoRatioBound_cut d hlam0 (le_of_lt hnmN)
  obtain ⟨hctrlZ, _⟩ := stoppedControls_pair_cut M C1 C2' alpha step m n omega hstop
    z hzgrid hz
  have hinfl : Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ)) ≤
      (2 * Section6Stopping.holderStoppingLambda C1 alpha) *
        ((m : ℝ) - ((gate + 1 : ℕ) : ℝ)) := by
    refine stopping_inflation_of_gap hlam0 (by omega) ?_
    have hgap : 2 * ((K : ℝ) + 5) ≤ (m : ℝ) - (n : ℝ) := by
      have h' : n + 2 * K + 11 ≤ m := by omega
      have h'' : (n : ℝ) + 2 * (K : ℝ) + 11 ≤ (m : ℝ) := by exact_mod_cast h'
      linarith
    have hgate : ((gate + 1 : ℕ) : ℝ) ≤ (n : ℝ) + (K : ℝ) + 5 := by
      exact_mod_cast (show gate + 1 ≤ n + K + 5 by omega)
    linarith
  have hratio := stoppedRatio_row_cut (L := L) M C1 C2' alpha step m n top omega
    hnmN htopm hlam0 hlam1 heps0 hdelta z hz hstop hzgrid
  have hcontr := hcontract
    (Section6Stopping.holderStoppingEpsilon C2' alpha) heps0 (by
      rw [Section6Stopping.holderStoppingEpsilon]
      have hC2pos : (0 : ℝ) < C2 := by linarith
      have hC2'pos : (0 : ℝ) < C2' := by linarith
      have hsq : Real.sqrt (1 - alpha) ≤ 1 := by
        have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith [halpha.1]
        simpa using Real.sqrt_le_sqrt h1
      calc
        C2'⁻¹ * Real.sqrt (1 - alpha) ≤ C2'⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = C2'⁻¹ := by ring
        _ ≤ C2⁻¹ := inv_anti₀ hC2pos hC2ge)
  have hfamZ := hfam M hsmall (Section6Stopping.holderStoppingEpsilon C2' alpha)
    hepsIcc (Section6Stopping.holderStoppingLambda C1 alpha)
    (2 * Section6Stopping.holderStoppingLambda C1 alpha) (by linarith)
    (by linarith) (by linarith) k hk ((3 : ℝ) ^ (-(1 / 4 : ℝ)))
    hthetaIoo hthetak hcontr
    L m n (gate + 1) top (by omega) (by omega) htopm z hz omega
    hctrlZ.1 hctrlZ.2 hinfl (rowTwoRatioBound_cut d C1 alpha m n) hR0
    (fun j hj ↦ by
      refine hratio j ?_
      rw [Finset.mem_Icc] at hj ⊢
      omega)
    u h g hsol hg hh
  dsimp only at hfamZ
  rw [show ((gate + 1 : ℕ) : ℤ) = (gate : ℤ) + 1 from by push_cast; ring,
    ← hKepsDef, ← hKforceDef, ← hKboundaryDef] at hfamZ
  have hsub : truncatedCube d (m : ℤ) (gate : ℤ) x ⊆
      truncatedCube d (m : ℤ) ((gate : ℤ) + 1) z := by
    refine truncatedCube_subset_of_dist ?_
    intro i
    refine (hdist i).trans ?_
    have hle : (3 : ℝ) ^ (n : ℤ) ≤ (3 : ℝ) ^ (gate : ℤ) := by
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hpow : (3 : ℝ) ^ (n : ℕ) = (3 : ℝ) ^ (n : ℤ) := by rw [zpow_natCast]
    have h3 : (3 : ℝ) ^ ((gate : ℤ) + 1) = 3 * (3 : ℝ) ^ (gate : ℤ) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; ring
    rw [hpow, h3]
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (gate : ℤ) := by positivity
    linarith
  have htrans := normalizedL2On_sub_average_crossCentre_le (d := d) (m := (m : ℤ))
    (j := (gate : ℤ)) (ell := (gate : ℤ) + 1) hx hz (by omega) (by omega) hsub u
  rw [show (gate : ℤ) + 1 - (gate : ℤ) + 2 = (3 : ℤ) by ring] at htrans
  have hcompose := oscillationLeg_compose (j := (gate : ℤ)) (top := (top : ℤ))
    htrans hfamZ (Real.sqrt_nonneg _)
  rw [show (3 : ℝ) * Real.sqrt (((3 : ℝ) ^ (3 : ℤ)) ^ d) = oscillationLegPrice d
    from rfl] at hcompose
  set S : ℝ := Real.sqrt (tailAverage M L (gate + 2) omega
    (translatedCube d ((gate : ℤ) + 2) z)) with hSDef
  set R : ℝ := rowTwoRatioBound_cut d C1 alpha m n with hRDef
  set w : ℝ := Section6Stopping.holderStoppingLambda C1 alpha *
    ((m : ℝ) - (n : ℝ) + 1) with hwDef
  set DataG : ℝ := (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
    (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d (m : ℤ)) (1 / 2) g
    with hDataGDef
  set DataH : ℝ := (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
    (3 : ℝ) ^ ((m : ℝ) / 2) *
    fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ)) (1 / 2) h.grad
    with hDataHDef
  have hw0 : 0 ≤ w := by
    rw [hwDef]
    have hgap : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) + 1 := by
      have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show n ≤ m by omega)
      linarith
    positivity
  have hDataG0 : 0 ≤ DataG := by
    rw [hDataGDef]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
        (Real.rpow_nonneg (by norm_num) _))
      (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  have hDataH0 : 0 ≤ DataH := by
    rw [hDataHDef]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
        (Real.rpow_nonneg (by norm_num) _))
      (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
  have hStf := rowTwo_data_pairing_cut M C1 C2' alpha step m n (gate + 2) L omega z
    hzgrid hz hstop hnmN (by omega) (by omega) hlam0 hlam1 heps0 hdelta g hg
  have hSup := sqrt_tailAverage_mul_vectorSupNorm_le_boundaryDatum_cutoff
    M C1 C2' alpha step m n (gate + 2) L omega z hzgrid hz hstop hnmN
    (by omega) (by omega) hlam0 hlam1 heps0 hdelta h hh
  have hTop := sqrt_tailAverage_mul_topBoundary_le_boundaryDatum_cutoff
    M C1 C2' alpha step m n (gate + 2) top L omega z hzgrid hz hstop hnmN
    (by omega) (by omega) (by omega) hlam0 hlam1 heps0 hdelta h hh
  rw [show ((gate + 2 : ℕ) : ℤ) = (gate : ℤ) + 2 from by push_cast; ring,
    ← hSDef, ← hRDef, ← hDataGDef] at hStf
  rw [show ((gate + 2 : ℕ) : ℤ) = (gate : ℤ) + 2 from by push_cast; ring,
    ← hSDef, ← hRDef, ← hDataHDef] at hSup hTop
  let I : ℝ := if BoundaryTouches (truncatedCube d (m : ℤ) (top : ℤ) z)
    (cube d (m : ℤ)) then 1 else 0
  have hI0 : 0 ≤ I := by dsimp only [I]; split_ifs <;> norm_num
  have hI1 : I ≤ 1 := by dsimp only [I]; split_ifs <;> norm_num
  have hdec0 : 0 ≤ (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) := by positivity
  have hdec1 : (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    simp only [neg_nonpos]
    have htm : (top : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show top ≤ m by omega)
    linarith
  have hforcePair : S *
      ((3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
        (tailCoefficientCubeAverage M L m omega)⁻¹ *
        (3 : ℝ) ^ ((m : ℝ) / 2) *
        holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) ≤ R * DataG := by
    have hbinv : 0 ≤ (tailCoefficientCubeAverage M L m omega)⁻¹ :=
      inv_nonneg.mpr (tailCoefficientCubeAverage_pos M L m omega).le
    have hsemi : 0 ≤ holderSeminormOn (cube d (m : ℤ)) (1 / 2) g :=
      Section6ExcessDecay.holderSeminormOn_nonneg hg
    have hrest : 0 ≤ (tailCoefficientCubeAverage M L m omega)⁻¹ *
        (3 : ℝ) ^ ((m : ℝ) / 2) *
        holderSeminormOn (cube d (m : ℤ)) (1 / 2) g := by positivity
    calc
      _ = S * ((3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
          ((tailCoefficientCubeAverage M L m omega)⁻¹ *
            (3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) g)) := by ring
      _ ≤ S * (1 * ((tailCoefficientCubeAverage M L m omega)⁻¹ *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hdec1 hrest) (Real.sqrt_nonneg _)
      _ = S * ((tailCoefficientCubeAverage M L m omega)⁻¹ *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by ring
      _ ≤ R * DataG := hStf
  have hEbudget : 3 * Keps *
      (2 * Section6Stopping.holderStoppingLambda C1 alpha) *
      ((m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1) ≤ 6 * Keps * w := by
    have hscale : (m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1 ≤
        (m : ℝ) - (n : ℝ) + 1 := by
      have : (n : ℝ) ≤ ((gate + 1 : ℕ) : ℝ) := by exact_mod_cast (show n ≤ gate + 1 by omega)
      linarith
    rw [hwDef]
    calc
      3 * Keps * (2 * Section6Stopping.holderStoppingLambda C1 alpha) *
          ((m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1) =
        (6 * Keps * Section6Stopping.holderStoppingLambda C1 alpha) *
          ((m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1) := by ring
      _ ≤ (6 * Keps * Section6Stopping.holderStoppingLambda C1 alpha) *
          ((m : ℝ) - (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = 6 * Keps *
          (Section6Stopping.holderStoppingLambda C1 alpha *
            ((m : ℝ) - (n : ℝ) + 1)) := by ring
  let Abar : ℝ := Citer * ((k : ℝ) + 1) *
      ((k : ℝ) + 2 + 2 * Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - ((gate + 1 : ℕ) : ℝ))) +
    Citer * (3 * Keps * (2 * Section6Stopping.holderStoppingLambda C1 alpha) *
      ((m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1))
  let D : ℝ :=
    5 / 2 * Kforce * (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) * R *
        ((tailCoefficientCubeAverage M L m omega)⁻¹ *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) +
      Kmean * (3 * Keps * (2 * Section6Stopping.holderStoppingLambda C1 alpha) *
          ((m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1)) *
        vectorSupNormOn (cube d (m : ℤ)) h.grad * I +
      5 / 2 * Kboundary * (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad) * I
  have hcomposeFinal :
      (3 : ℝ) ^ (-(gate : ℤ)) *
          normalizedL2On (truncatedCube d (m : ℤ) (gate : ℤ) x)
            (fun p ↦ u.toFun p -
              averageOn (truncatedCube d (m : ℤ) (gate : ℤ) x) u.toFun) ≤
        oscillationLegPrice d * (Real.exp Abar *
          ((3 : ℝ) ^ (-(top : ℤ)) *
            normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
              (fun p ↦ u.toFun p -
                averageOn (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun) + D)) := by
    simpa only [Abar, D, I, R] using hcompose
  refine ⟨Abar, D, ?_, hcomposeFinal, ?_⟩
  · have hc1 : 0 ≤ 2 * Citer * ((k : ℝ) + 1) := by positivity
    have hc2 : 0 ≤ 6 * Citer * Keps := by positivity
    have hnGateR : (n : ℝ) ≤ ((gate + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ gate + 1 by omega)
    have e1 : Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - ((gate + 1 : ℕ) : ℝ)) ≤ w := by
      rw [hwDef]
      exact mul_le_mul_of_nonneg_left (by linarith [hnGateR]) hlam0
    have e2 : Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1) ≤ w := by
      rw [hwDef]
      exact mul_le_mul_of_nonneg_left (by linarith [hnGateR]) hlam0
    dsimp only [Abar]
    nlinarith only [mul_le_mul_of_nonneg_left e1 hc1,
      mul_le_mul_of_nonneg_left e2 hc2]
  · dsimp only [D]
    have hFterm0 : 0 ≤
        (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
          (tailCoefficientCubeAverage M L m omega)⁻¹ *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hdec0
            (inv_nonneg.mpr (tailCoefficientCubeAverage_pos M L m omega).le))
          (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) ((m : ℝ) / 2)))
        (Section6ExcessDecay.holderSeminormOn_nonneg hg)
    have hBoundaryTerm0 : 0 ≤
        (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad) := by
      exact mul_nonneg hdec0 (mul_nonneg
        (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) ((m : ℝ) / 2))
        (Section6ExcessDecay.holderSeminormOn_nonneg hh))
    have hbound := boundaryDefectBudget_bound
      (S := S) (Kforce := Kforce) (Kmean := Kmean) (Keps := Keps)
      (Kboundary := Kboundary) (R := R) (w := w) (DataG := DataG)
      (DataH := DataH) (I := I)
      (F := (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
        (tailCoefficientCubeAverage M L m omega)⁻¹ *
        (3 : ℝ) ^ ((m : ℝ) / 2) *
        holderSeminormOn (cube d (m : ℤ)) (1 / 2) g)
      (MeanTerm := vectorSupNormOn (cube d (m : ℤ)) h.grad)
      (BoundaryTerm := (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad))
      (E := 3 * Keps * (2 * Section6Stopping.holderStoppingLambda C1 alpha) *
        ((m : ℝ) - ((gate + 1 : ℕ) : ℝ) + 1))
      hKforce0 hKmean0 hKeps0
      hKboundary0 (by rw [hRDef]; exact hR0) (by rw [hRDef]; exact hR1)
      hw0 hDataG0 hDataH0 hI0 hI1 (Real.sqrt_nonneg _)
      hFterm0
      (Section6Holder.vectorSupNormOn_cube_nonneg hh)
      hBoundaryTerm0
      hEbudget hforcePair hSup hTop
    rw [hSDef, hRDef, hwDef, hDataGDef, hDataHDef] at hbound
    convert hbound using 1
    all_goals ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
