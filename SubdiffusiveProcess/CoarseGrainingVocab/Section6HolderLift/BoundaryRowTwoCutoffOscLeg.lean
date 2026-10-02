import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffFamilyLeg
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffTopLeg




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

noncomputable section
attribute [local instance] Classical.propDecidable

theorem aux_dedup_d162_boundaryKsum_bound {R TP w Kosc Kf X : ℝ}
    (hKosc : 0 ≤ Kosc) (hKf : 0 ≤ Kf)
    (hRTP : R * TP ≤ X) (hdatum : (1 + w) * R ^ 2 ≤ X) :
    R * (Kosc * TP) + Kf * (1 + w) * R ^ 2 ≤ (Kosc + Kf) * X := by
  calc
    R * (Kosc * TP) + Kf * (1 + w) * R ^ 2 =
        Kosc * (R * TP) + Kf * ((1 + w) * R ^ 2) := by ring
    _ ≤ Kosc * X + Kf * X :=
      add_le_add (mul_le_mul_of_nonneg_left hRTP hKosc)
        (mul_le_mul_of_nonneg_left hdatum hKf)
    _ = (Kosc + Kf) * X := by ring

private theorem boundaryKsum_bound {R TP w Kosc Kf X : ℝ}
    (hKosc : 0 ≤ Kosc) (hKf : 0 ≤ Kf)
    (hRTP : R * TP ≤ X) (hdatum : (1 + w) * R ^ 2 ≤ X) :
    R * (Kosc * TP) + Kf * (1 + w) * R ^ 2 ≤ (Kosc + Kf) * X := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.aux_dedup_d162_boundaryKsum_bound (R := R) (TP := TP) (w := w) (Kosc := Kosc) (Kf := Kf) (X := X) (hKosc := hKosc) (hKf := hKf) (hRTP := hRTP) (hdatum := hdatum)

/-- The complete oscillation contribution for a center anywhere in the domain
cube. -/
theorem exists_boundaryRowTwoCutoffOscLeg (d : ℕ) [NeZero d]
    (hExcess : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
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
      ∀ step L m n gate K : ℕ,
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ z x : Vec d, OnTriadicGrid n z → z ∈ cube d (m : ℤ) →
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
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
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
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) g +
              (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
                  (1 / 2) h.grad) := by
  classical
  obtain ⟨C2, A0f, Pf, Kf, hC2, hA0f, hPf, hKf, hfamLeg⟩ :=
    exists_boundaryRowTwoCutoffFamilyLeg d hExcess
  obtain ⟨Kosc, hKosc, htopleg⟩ := exists_boundaryRowTwoCutoffTopLegAt d
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hr0 : (0 : ℝ) ≤ ratioRate_cut d := ratioRate_nonneg_cut d
  have hdlog0 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by positivity
  refine ⟨C2, A0f + 8 * (d : ℝ) * Real.log 3,
    Pf + 2 * ratioRate_cut d + (d : ℝ) * Real.log 3 + 1,
    oscillationLegPrice d * (Kosc + Kf), hC2, by positivity, by positivity,
    mul_nonneg (oscillationLegPrice_nonneg d) (add_nonneg hKosc hKf), ?_⟩
  intro C2' hC2ge M hsmall C1 alpha halpha hepsIcc hdelta heps8 hlam0 hlam1
    step L m n gate K omega z x hzgrid hz hx hdist hstop hngate hgateK hKub
    hroom hroomBig u h g hsol hg hh
  have hC2' : 1 ≤ C2' := hC2.trans hC2ge
  have hnm : n < m := by omega
  have heps0 : 0 ≤ Section6Stopping.holderStoppingEpsilon C2' alpha :=
    holderStoppingEpsilon_nonneg (by linarith)
  have heps1 : Section6Stopping.holderStoppingEpsilon C2' alpha ≤ 1 :=
    holderStoppingEpsilon_le_one hC2' halpha.1
  have hR0 : 0 ≤ rowTwoRatioBound_cut d C1 alpha m n :=
    rowTwoRatioBound_nonneg_cut d C1 alpha m n
  have hgap0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_of_lt hnm)
    linarith
  set w : ℝ := Section6Stopping.holderStoppingLambda C1 alpha *
    ((m : ℝ) - (n : ℝ) + 1) with hwDef
  have hw0 : 0 ≤ w := by rw [hwDef]; positivity
  have hlamgap : Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ)) ≤ w := by
    rw [hwDef]
    exact mul_le_mul_of_nonneg_left (by linarith) hlam0
  obtain ⟨top, hntop, htopm, hmtop, htop⟩ := htopleg M hsmall C1 C2' alpha
    heps0 heps1 hlam0 hlam1 hdelta step L m n K (gate + 2) omega z hzgrid hz
    hstop (by omega) hroom hnm (by omega) (by omega) u
  rw [show ((gate + 2 : ℕ) : ℤ) = (gate : ℤ) + 2 from by push_cast; ring] at htop
  obtain ⟨Abar, D, hAbar, hcompose, hD⟩ := hfamLeg C2' hC2ge M hsmall C1
    alpha halpha hepsIcc hdelta heps8 hlam0 hlam1 step L m n gate K top
    omega z x hzgrid hz hx hdist hstop hngate hgateK hroomBig (by omega) htopm
    u h g hsol hg hh
  set Eg : ℝ := vectorNormalizedL2On (cube d (m : ℤ))
    (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p)
  set DataG : ℝ := (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
    (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d (m : ℤ)) (1 / 2) g
  set DataH : ℝ := (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
    (3 : ℝ) ^ ((m : ℝ) / 2) *
    fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ)) (1 / 2) h.grad
  have hEg0 : 0 ≤ Eg := by dsimp only [Eg]; exact Real.sqrt_nonneg _
  have hDataG0 : 0 ≤ DataG := by
    dsimp only [DataG]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
        (Real.rpow_nonneg (by norm_num) _))
      (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  have hDataH0 : 0 ≤ DataH := by
    dsimp only [DataH]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
        (Real.rpow_nonneg (by norm_num) _))
      (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
  have hKtop0 : 0 ≤ rowTwoRatioBound_cut d C1 alpha m n *
      (Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ))) :=
    mul_nonneg hR0 (mul_nonneg hKosc (scaleTransferPrice_nonneg d _))
  have hKdat0 : 0 ≤ Kf * (1 + w) * rowTwoRatioBound_cut d C1 alpha m n ^ 2 := by
    positivity
  have harith := rowTwo_oscLeg_arith (oscillationLegPrice_nonneg d)
    (Real.exp_nonneg _) (Real.sqrt_nonneg _) hcompose htop hD hKtop0 hKdat0
    hEg0 (add_nonneg hDataG0 hDataH0)
  refine harith.trans ?_
  have hRexp : rowTwoRatioBound_cut d C1 alpha m n ≤
      Real.exp (ratioRate_cut d * w) := by
    rw [rowTwoRatioBound_cut]
    refine Real.exp_le_exp.mpr ?_
    calc
      ratioRate_cut d * Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) =
        ratioRate_cut d * (Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ))) := by ring
      _ ≤ ratioRate_cut d * w := mul_le_mul_of_nonneg_left hlamgap hr0
  have hKw : (K : ℝ) ≤ w + 1 := by linarith
  have hTP : scaleTransferPrice d ((m : ℤ) - (top : ℤ)) ≤
      Real.exp (8 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) * w) := by
    refine scaleTransferPrice_le_exp d (by omega) ?_
    rw [show (((m : ℤ) - (top : ℤ) : ℤ) : ℝ) = (m : ℝ) - (top : ℝ)
      from by push_cast; ring]
    have hmt : (m : ℝ) - (top : ℝ) ≤ (K : ℝ) + 5 := by
      have : (m : ℝ) ≤ (top : ℝ) + (K : ℝ) + 5 := by exact_mod_cast hmtop
      linarith
    have hbase : (m : ℝ) - (top : ℝ) + 2 ≤ w + 8 := by linarith
    calc
      ((m : ℝ) - (top : ℝ) + 2) * (d : ℝ) * Real.log 3 =
          ((m : ℝ) - (top : ℝ) + 2) * ((d : ℝ) * Real.log 3) := by ring
      _ ≤ (w + 8) * ((d : ℝ) * Real.log 3) :=
        mul_le_mul_of_nonneg_right hbase hdlog0
      _ = 8 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) * w := by ring
  set X : ℝ := Real.exp (8 * (d : ℝ) * Real.log 3 +
    (2 * ratioRate_cut d + (d : ℝ) * Real.log 3 + 1) * w)
  have hRTP : rowTwoRatioBound_cut d C1 alpha m n *
      scaleTransferPrice d ((m : ℤ) - (top : ℤ)) ≤ X := by
    refine (mul_le_exp_add (scaleTransferPrice_nonneg d _) hRexp hTP).trans ?_
    dsimp only [X]
    exact Real.exp_le_exp.mpr (by nlinarith only [hr0, hw0, hdlog0])
  have honew : 1 + w ≤ Real.exp w := by
    simpa [add_comm] using Real.add_one_le_exp w
  have hRtwo : rowTwoRatioBound_cut d C1 alpha m n ^ 2 ≤
      Real.exp (2 * ratioRate_cut d * w) := by
    calc
      rowTwoRatioBound_cut d C1 alpha m n ^ 2 =
          rowTwoRatioBound_cut d C1 alpha m n * rowTwoRatioBound_cut d C1 alpha m n := by ring
      _ ≤ Real.exp (ratioRate_cut d * w) * Real.exp (ratioRate_cut d * w) :=
        mul_le_mul hRexp hRexp hR0 (Real.exp_nonneg _)
      _ = Real.exp (2 * ratioRate_cut d * w) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hdatum : (1 + w) * rowTwoRatioBound_cut d C1 alpha m n ^ 2 ≤ X := by
    refine (mul_le_exp_add (by positivity) honew hRtwo).trans ?_
    dsimp only [X]
    have hdlw : 0 ≤ ((d : ℝ) * Real.log 3) * w := mul_nonneg hdlog0 hw0
    exact Real.exp_le_exp.mpr (by nlinarith only [hdlog0, hdlw])
  have hKsum := boundaryKsum_bound hKosc hKf hRTP hdatum
  have hKnorm :
      rowTwoRatioBound_cut d C1 alpha m n *
          (Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ))) +
          Kf * (1 + w) * rowTwoRatioBound_cut d C1 alpha m n ^ 2 ≤
        (Kosc + Kf) * Real.exp (8 * (d : ℝ) * Real.log 3 +
          (2 * ratioRate_cut d + (d : ℝ) * Real.log 3 + 1) * w) := by
    dsimp only [X] at hKsum
    exact hKsum
  have hcollapse := rowTwo_collapse_arith
    (Kfac := Kosc + Kf)
    (a1 := A0f + Pf * w)
    (a2 := 8 * (d : ℝ) * Real.log 3 +
      (2 * ratioRate_cut d + (d : ℝ) * Real.log 3 + 1) * w)
    (a3 := A0f + 8 * (d : ℝ) * Real.log 3 +
      (Pf + 2 * ratioRate_cut d + (d : ℝ) * Real.log 3 + 1) * w)
    (oscillationLegPrice_nonneg d) (add_nonneg hEg0 (add_nonneg hDataG0 hDataH0))
    (add_nonneg hKtop0 hKdat0) (Real.exp_le_exp.mpr hAbar) hKnorm (by ring)
  simpa only [hwDef, Eg, DataG, DataH, add_assoc] using hcollapse

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
