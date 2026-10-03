module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoAbsorb
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoForcingLeg
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoConversion
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffDataLegs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffOscLeg
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffGateBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.SharedStoppingParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoGateScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.StoppingWindows

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Row two for points in the full cube.  This outer estimate retains the
boundary datum; the final package uses the sharper interior row whenever the
point lies in the inner cube. -/
theorem exists_boundaryRowTwoCutoffOuterAtStepFree (d : ℕ) [NeZero d]
    (hExcess : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ (C1min C2min Crow : ℝ), 2 ≤ C1min ∧ C1min ≤ C2min ∧ 0 ≤ Crow ∧
      ∀ C1 C2 : ℝ, C1min ≤ C1 → C2min ≤ C2 → C1 ≤ C2 →
      ∀ step : ℕ, 21 ≤ step →
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ L m : ℕ, L < m →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (originCube d (m : ℤ)) u h g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
      ∀ n : ℕ,
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
      ∀ x : Vec d, x ∈ cube d (m : ℤ) →
        vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) ≤
          Crow * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
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
  obtain ⟨C2min, A0osc, Posc, Kpre, hC2min, hA0osc, hPosc, hKpre, hosc⟩ :=
    exists_boundaryRowTwoCutoffOscLeg d hExcess
  obtain ⟨Kb, hKb, hgateBudget⟩ := exists_boundaryRowTwoCutoffGateBudget d
  have hr0 : (0 : ℝ) ≤ ratioRate_cut d := ratioRate_nonneg_cut d
  have hdlog0 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by positivity
  set A0f : ℝ := A0osc + 3 * (d : ℝ) * Real.log 3 with hA0fDef
  set Pf : ℝ := Posc + ratioRate_cut d + (d : ℝ) * Real.log 3 with hPfDef
  have hPf0 : 0 ≤ Pf := by rw [hPfDef]; linarith
  obtain ⟨C1abs, Cabs, hC1abs, hCabs, habsorb⟩ :=
    Section6Holder.exists_holderExponentialAbsorption A0f Pf hPf0
  let Kdata := 1 + rowTwoForcingConst_cut d + rowTwoCutoffBoundaryFractionalConst d
  refine ⟨max C1abs 2, max C2min (max C1abs 2),
    Real.sqrt ((81 : ℝ) ^ d * Kb) * (Kpre + Kdata) * Cabs,
    le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · have hdata : 0 ≤ Kdata := by
      dsimp only [Kdata]
      exact add_nonneg
        (add_nonneg zero_le_one (rowTwoForcingConst_nonneg_cut d))
        (rowTwoCutoffBoundaryFractionalConst_nonneg d)
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hKpre hdata)) hCabs.le
  intro C1 C2 hC1thr hC2thr hC1C2 step hstep21 M hsmall alpha halpha hepsIcc
    hdelta L m hLm omega u h g hsol hg hh n hstop x hx
  set lam : ℝ := Section6Stopping.holderStoppingLambda C1 alpha with hlamDef
  have hC12 : (2 : ℝ) ≤ C1 := le_trans (le_max_right C1abs 2) hC1thr
  have hC2ge : C2min ≤ C2 :=
    le_trans (le_max_left C2min (max C1abs 2)) hC2thr
  have hC2one : (1 : ℝ) ≤ C2 := by linarith
  obtain ⟨hlam0raw, hlam1raw, heps8⟩ :=
    holderStopping_conditions_of_coupled hC12 hC1C2 halpha
  have hlam0 : 0 ≤ lam := by simpa only [hlamDef] using hlam0raw
  have hlam1 : lam < 1 := by simpa only [hlamDef] using hlam1raw
  have heps0 : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha :=
    holderStoppingEpsilon_nonneg (by linarith : (0 : ℝ) ≤ C2)
  have habsorbC1 := holderExponentialAbsorption_mono hPf0 hC1abs
    (le_trans (le_max_left C1abs 2) hC1thr) habsorb
  have hgapZ : ((step : ℤ) + 5) ≤ (m : ℤ) - (n : ℤ) :=
    gap_ge_step_of_stopping_cut M alpha _ _ step m n omega hstop
  have hgapN : n + 26 ≤ m := by omega
  have hgapR : (26 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have h : (n : ℝ) + 26 ≤ (m : ℝ) := by exact_mod_cast hgapN
    linarith
  have hgapR0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by linarith
  have hlamQuarter : lam ≤ 1 / 4 := by
    rw [hlamDef, Section6Stopping.holderStoppingLambda]
    have hinv : C1⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      exact inv_anti₀ (by norm_num) hC12
    have hinv0 : (0 : ℝ) ≤ C1⁻¹ := by positivity
    have ha0 : (0 : ℝ) ≤ 1 - alpha := by linarith [halpha.2]
    have ha2 : (1 : ℝ) - alpha ≤ 1 / 2 := by linarith [halpha.1]
    nlinarith only [hinv, hinv0, ha0, ha2]
  set K : ℕ := ⌈lam * ((m : ℝ) - (n : ℝ))⌉₊ with hKDef
  have hKlow : lam * ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) := by
    rw [hKDef]
    exact Nat.le_ceil _
  have hKup : (K : ℝ) < lam * ((m : ℝ) - (n : ℝ)) + 1 := by
    rw [hKDef]
    exact Nat.ceil_lt_add_one (mul_nonneg hlam0 hgapR0)
  have hKub : (K : ℝ) ≤ lam * ((m : ℝ) - (n : ℝ)) + 1 := le_of_lt hKup
  have hroom : 1 + lam * ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1 := by linarith
  have hroomBigR : (n : ℝ) + 2 * (K : ℝ) + 11 < (m : ℝ) := by
    have h1 : lam * ((m : ℝ) - (n : ℝ)) ≤
        1 / 4 * ((m : ℝ) - (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hlamQuarter hgapR0
    linarith
  have hroomBig : n + 2 * K + 11 < m := by exact_mod_cast hroomBigR
  obtain ⟨z, hzgrid, hz, hdist⟩ := Section6Holder.exists_holderGridCentre
    (d := d) (m := m) (n := n) (x := x) hx (by omega)
  obtain ⟨gate, hngate, hgateK, hgood⟩ := exists_interiorRowTwoGateScale_cut M C1 C2
    alpha step m n K omega z hzgrid hz hstop hC2one halpha.1 (by omega)
    (by rw [← hlamDef]; exact hKlow)
  have hsIcc : (interiorFractionalOrder).1 ∈
      Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) := by
    rw [Section6HolderInterior.interiorFractionalOrder_val]
    refine ⟨?_, le_rfl⟩
    have hS : Section6Stopping.holderStoppingS = 1 / 32 := rfl
    rw [hS] at hsmall
    linarith
  have hbudget := hgateBudget M hsIcc L m n gate hngate (by omega) x z omega
    hx hz hdist hgood u h g hsol hg hh
  have hsigmaPos : 0 < tailAverage M L (gate + 2) omega
      (translatedCube d ((gate : ℤ) + 2) z) := by
    rw [show ((gate : ℤ) + 2) = ((gate + 2 : ℕ) : ℤ) by omega]
    exact tailAverage_translatedCube_pos_cut M L (gate + 2) omega z
  have hOscLeg := hosc C2 hC2ge M hsmall C1 alpha halpha hepsIcc hdelta heps8
    hlam0 hlam1 step L m n gate K omega z x hzgrid hz hx hdist hstop hngate
    hgateK (by rw [← hlamDef]; exact hKub) (by rw [← hlamDef]; exact hroom)
    hroomBig u h g hsol hg hh
  have hForceLeg := interiorRowTwo_forcingLeg_cut M C1 C2 alpha step m n gate L omega
    z x hzgrid hz hx hstop (by omega) (by omega) (by omega) hlam0 hlam1
    heps0 hdelta g hg
  have hMeanLeg := boundaryRowTwoCutoff_meanLeg M C1 C2 alpha step m n gate L omega
    z x hzgrid hz hx hstop (by omega) (by omega) (by omega) hlam0 hlam1
    heps0 hdelta h hh
  have hFracLeg := boundaryRowTwoCutoff_fractionalLeg M C1 C2 alpha step m n gate L omega
    z x hzgrid hz hx hstop (by omega) (by omega) (by omega) hlam0 hlam1
    heps0 hdelta h hh
  let Eg := vectorNormalizedL2On (cube d (m : ℤ))
    (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p)
  let DataG := (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
    (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d (m : ℤ)) (1 / 2) g
  let DataH := (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
    (3 : ℝ) ^ ((m : ℝ) / 2) *
    fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
      (1 / 2) h.grad
  let Total := Eg + DataG + DataH
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
  have hT0 : 0 ≤ Total := by dsimp only [Total]; linarith
  have hGtoT : DataG ≤ Total := by dsimp only [Total]; linarith
  have hHtoT : DataH ≤ Total := by dsimp only [Total]; linarith
  let sigma := tailAverage M L (gate + 2) omega
    (translatedCube d ((gate : ℤ) + 2) z)
  let O := normalizedL2On (truncatedCube d (m : ℤ) (gate : ℤ) x)
    (fun q ↦ u.toFun q - averageOn (truncatedCube d (m : ℤ) (gate : ℤ) x) u.toFun)
  let A := Real.sqrt sigma * (3 : ℝ) ^ (-(gate : ℤ)) * O
  let G := Real.sqrt sigma * Real.sqrt (vecNormSq
    (averageVecOn (truncatedCube d (m : ℤ) (gate : ℤ) x) h.grad))
  let F := (interiorFractionalOrder).1 ^ (-6 : ℝ) * (Real.sqrt sigma)⁻¹ *
    (3 : ℝ) ^ ((interiorFractionalOrder).1 * (gate : ℝ)) *
    (fractionalSeminormOn (truncatedCube d (m : ℤ) (gate : ℤ) x)
      (interiorFractionalOrder).1 g).toReal
  let H := Real.sqrt sigma * (interiorFractionalOrder).1 ^ (-2 : ℝ) *
    (3 : ℝ) ^ ((interiorFractionalOrder).1 * (gate : ℝ)) *
    (fractionalSeminormOn (truncatedCube d (m : ℤ) (gate : ℤ) x)
      (interiorFractionalOrder).1 h.grad).toReal
  let AO := Kpre * Real.exp (A0osc + Posc *
    (lam * ((m : ℝ) - (n : ℝ) + 1)))
  let B := Kdata * rowTwoRatioBound_cut d C1 alpha m n
  have hAO : A ≤ AO * Total := by
    dsimp only [A, AO, sigma, O, Total, Eg, DataG, DataH]
    rw [← mul_assoc] at hOscLeg
    simpa only [hlamDef] using hOscLeg
  have hAF : F ≤ rowTwoForcingConst_cut d * rowTwoRatioBound_cut d C1 alpha m n * Total := by
    dsimp only [F, sigma]
    exact hForceLeg.trans (mul_le_mul_of_nonneg_left hGtoT
      (mul_nonneg (rowTwoForcingConst_nonneg d)
        (rowTwoRatioBound_nonneg_cut d C1 alpha m n)))
  have hAG : G ≤ rowTwoRatioBound_cut d C1 alpha m n * Total := by
    dsimp only [G, sigma]
    exact hMeanLeg.trans (mul_le_mul_of_nonneg_left hHtoT
      (rowTwoRatioBound_nonneg d C1 alpha m n))
  have hAH : H ≤ rowTwoCutoffBoundaryFractionalConst d *
      rowTwoRatioBound_cut d C1 alpha m n * Total := by
    dsimp only [H, sigma]
    exact hFracLeg.trans (mul_le_mul_of_nonneg_left hHtoT
      (mul_nonneg (rowTwoCutoffBoundaryFractionalConst_nonneg d)
        (rowTwoRatioBound_nonneg d C1 alpha m n)))
  have hsum : A + G + F + H ≤ (AO + B) * Total := by
    have hs := add_le_add (add_le_add (add_le_add hAO hAG) hAF) hAH
    dsimp only [B, Kdata]
    nlinarith only [hs]
  have hread := sqrt_harmonicPhysicalFourBudgets_le_legs M L m gate z x omega
    (s := (interiorFractionalOrder).1) (K := (81 : ℝ) ^ d * Kb)
    (by rw [Section6HolderInterior.interiorFractionalOrder_val]; norm_num)
    (by positivity) u h g
  have hread' : Real.sqrt ((81 : ℝ) ^ d *
      (Kb * harmonicPhysicalFourBudgets M L m gate z x omega
        (interiorFractionalOrder).1 u h g)) ≤
      Real.sqrt ((81 : ℝ) ^ d * Kb) * (A + G + F + H) := by
    dsimp only [A, G, F, H, sigma, O]
    simpa only [mul_assoc] using hread
  have hconv : vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
      (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p) ≤
      scaleTransferPrice d ((gate : ℤ) - 4 - (n : ℤ)) *
        Real.sqrt ((81 : ℝ) ^ d * Kb) * ((AO + B) * Total) := by
    calc
      _ ≤ scaleTransferPrice d ((gate : ℤ) - 4 - (n : ℤ)) *
          Real.sqrt ((81 : ℝ) ^ d *
            (Kb * harmonicPhysicalFourBudgets M L m gate z x omega
              (interiorFractionalOrder).1 u h g)) := hbudget
      _ ≤ scaleTransferPrice d ((gate : ℤ) - 4 - (n : ℤ)) *
          (Real.sqrt ((81 : ℝ) ^ d * Kb) * (A + G + F + H)) :=
        mul_le_mul_of_nonneg_left hread'
          (scaleTransferPrice_nonneg d ((gate : ℤ) - 4 - (n : ℤ)))
      _ ≤ scaleTransferPrice d ((gate : ℤ) - 4 - (n : ℤ)) *
          (Real.sqrt ((81 : ℝ) ^ d * Kb) * ((AO + B) * Total)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _))
          (scaleTransferPrice_nonneg d ((gate : ℤ) - 4 - (n : ℤ)))
      _ = _ := by ring
  set wgt : ℝ := lam * ((m : ℝ) - (n : ℝ) + 1) with hwgtDef
  have hwgt0 : 0 ≤ wgt := by rw [hwgtDef]; positivity
  have hAO0 : 0 ≤ AO := by dsimp only [AO]; positivity
  have hB0 : 0 ≤ B := by
    dsimp only [B, Kdata]
    exact mul_nonneg
      (add_nonneg
        (add_nonneg zero_le_one (rowTwoForcingConst_nonneg_cut d))
        (rowTwoCutoffBoundaryFractionalConst_nonneg d))
      (rowTwoRatioBound_nonneg d C1 alpha m n)
  refine rowTwo_absorb_arith (Real.sqrt_nonneg _) hT0 hAO0 hB0 hconv
    (b := 3 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) * wgt)
    (a := A0osc + (Posc + ratioRate_cut d) * wgt) ?_ ?_ ?_ ?_
  · refine scaleTransferPrice_le_exp d (by omega) ?_
    rw [show (((gate : ℤ) - 4 - (n : ℤ) : ℤ) : ℝ) =
      (gate : ℝ) - 4 - (n : ℝ) by push_cast; ring]
    have hgR : (gate : ℝ) ≤ (n : ℝ) + 4 + (K : ℝ) := by exact_mod_cast hgateK
    have hbase : (gate : ℝ) - 4 - (n : ℝ) + 2 ≤ wgt + 3 := by
      rw [hwgtDef]
      have : lam * ((m : ℝ) - (n : ℝ)) ≤
          lam * ((m : ℝ) - (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0
      linarith
    calc
      ((gate : ℝ) - 4 - (n : ℝ) + 2) * (d : ℝ) * Real.log 3 =
          ((gate : ℝ) - 4 - (n : ℝ) + 2) * ((d : ℝ) * Real.log 3) := by ring
      _ ≤ (wgt + 3) * ((d : ℝ) * Real.log 3) :=
        mul_le_mul_of_nonneg_right hbase hdlog0
      _ = 3 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) * wgt := by ring
  · refine mul_le_mul_of_nonneg_left ?_ hKpre
    refine Real.exp_le_exp.mpr ?_
    rw [hwgtDef]
    nlinarith only [hr0, hwgt0]
  · refine mul_le_mul_of_nonneg_left ?_ (by
      dsimp only [Kdata]
      exact add_nonneg
        (add_nonneg zero_le_one (rowTwoForcingConst_nonneg_cut d))
        (rowTwoCutoffBoundaryFractionalConst_nonneg d))
    rw [rowTwoRatioBound_cut]
    refine Real.exp_le_exp.mpr ?_
    have h1 : ratioRate_cut d * lam * ((m : ℝ) - (n : ℝ)) ≤ ratioRate_cut d * wgt := by
      rw [hwgtDef]
      calc
        ratioRate_cut d * lam * ((m : ℝ) - (n : ℝ)) =
            ratioRate_cut d * (lam * ((m : ℝ) - (n : ℝ))) := by ring
        _ ≤ ratioRate_cut d * (lam * ((m : ℝ) - (n : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hr0
          exact mul_le_mul_of_nonneg_left (by linarith) hlam0
    nlinarith only [h1, hA0osc, hPosc, hwgt0]
  · have habs := habsorbC1 alpha halpha ((m : ℝ) - (n : ℝ)) hgapR0
    have heq : A0osc + (Posc + ratioRate_cut d) * wgt +
        (3 * (d : ℝ) * Real.log 3 + ((d : ℝ) * Real.log 3) * wgt) =
        A0f + Pf * (C1⁻¹ * (1 - alpha)) * (((m : ℝ) - (n : ℝ)) + 1) := by
      rw [hA0fDef, hPfDef, hwgtDef, hlamDef,
        Section6Stopping.holderStoppingLambda]
      ring
    rw [heq]
    refine habs.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCabs.le
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have ha0 : (0 : ℝ) ≤ 1 - alpha := by linarith [halpha.2]
    nlinarith only [ha0, hgapR0]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
