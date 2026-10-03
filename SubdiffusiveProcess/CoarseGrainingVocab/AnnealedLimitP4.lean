module

public import Homogenization.Book.Ch04.Theorems.DilationLaw
public import Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.NormalizedBlocks
public import Homogenization.Book.Ch05.Theorems.Section57.AnnealedLimit

@[expose] public section

/-!
# Annealed primal/starred limit identification from `(P4)`

The public Chapter 5 theorem `barSigmaLimit_eq_barSigmaStarLimit` is packaged
under the stronger quenched `GammaSigmaCoarseGrainedEllipticity` record.  The
proof of the equality itself uses only `(P4)` and the annealed convergence
theorem.  This module records that exact weaker interface.

PROVENANCE: adapted line-for-line from
`Algsuperdiff/Section3/Annealed/RunningDiffusivityBridge.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter Homogenization Set Homogenization.Book

noncomputable section

private theorem le_of_forall_le_one_add_mul
    {a b : ℝ} (hb : 0 ≤ b) (h : ∀ ε > 0, a ≤ (1 + ε) * b) : a ≤ b := by
  by_contra hle
  have hlt : b < a := lt_of_not_ge hle
  by_cases hb0 : b = 0
  · nlinarith [h 1 (by norm_num : (0 : ℝ) < 1)]
  · have hbpos : 0 < b := lt_of_le_of_ne' hb hb0
    let ε := (a - b) / (2 * b)
    have hε : 0 < ε := div_pos (sub_pos.mpr hlt) (mul_pos (by norm_num) hbpos)
    have hm : (1 + ε) * b = (a + b) / 2 := by
      dsimp [ε]
      field_simp [hbpos.ne']
      ring
    nlinarith [h ε hε]

private theorem exponentialDecay_tendsto_zero {alpha : ℝ} (ha : 0 < alpha) :
    Tendsto (fun n : ℕ => Real.rpow (3 : ℝ) (-alpha * (n : ℝ)))
      atTop (nhds (0 : ℝ)) := by
  have hl : Tendsto (fun n : ℕ => (-alpha) * (n : ℝ)) atTop atBot :=
    tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
  exact (tendsto_rpow_atBot_of_base_gt_one (3 : ℝ) (by norm_num)).comp hl

private theorem barSigma_range_bddBelow_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    BddBelow (range fun n : ℕ => hP.barSigmaAtScale hStruct (n : ℤ)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
    hP hStruct hP4 n).le

private theorem barSigmaStar_range_bddAbove_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    BddAbove (range fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ)) := by
  refine ⟨hP.barSigmaAtScale hStruct (0 : ℤ), ?_⟩
  rintro x ⟨n, rfl⟩
  exact (Ch05.Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
    hP hStruct hP4 n).trans
      ((Ch05.Section54.Pigeonhole.scalarChain_of_P4 hP hStruct hP4
        (Nat.zero_le n)).2.2)

theorem barSigmaAtScale_tendsto_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Tendsto (fun n : ℕ => hP.barSigmaAtScale hStruct (n : ℤ)) atTop
      (nhds (Ch05.Section57.barSigmaLimit hP hStruct)) := by
  simpa [Ch05.Section57.barSigmaLimit, iInf] using!
    tendsto_atTop_ciInf
      (fun _ _ hnm =>
        (Ch05.Section54.Pigeonhole.scalarChain_of_P4 hP hStruct hP4 hnm).2.2)
      (barSigma_range_bddBelow_of_P4 hP hStruct hP4)

private theorem barSigmaStarAtScale_tendsto_barSigmaStarLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Tendsto (fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ)) atTop
      (nhds (Ch05.Section57.barSigmaStarLimit hP hStruct)) := by
  simpa [Ch05.Section57.barSigmaStarLimit, iSup] using!
    tendsto_atTop_ciSup
      (fun _ _ hnm =>
        (Ch05.Section54.Pigeonhole.scalarChain_of_P4 hP hStruct hP4 hnm).1)
      (barSigmaStar_range_bddAbove_of_P4 hP hStruct hP4)

private theorem barSigmaStarAtScale_le_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) (n : ℕ) :
    hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
      Ch05.Section57.barSigmaLimit hP hStruct := by
  refine le_csInf (range_nonempty _) ?_
  rintro y ⟨m, rfl⟩
  by_cases hnm : n ≤ m
  · exact ((Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hnm).1).trans
        (Ch05.Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
          hP hStruct hP4 m)
  · have hmn : m ≤ n := by omega
    exact (Ch05.Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
      hP hStruct hP4 n).trans
        ((Ch05.Section54.Pigeonhole.scalarChain_of_P4
          hP hStruct hP4 hmn).2.2)

private theorem barSigmaStarLimit_le_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Ch05.Section57.barSigmaStarLimit hP hStruct ≤
      Ch05.Section57.barSigmaLimit hP hStruct := by
  refine csSup_le (range_nonempty _) ?_
  rintro x ⟨n, rfl⟩
  exact barSigmaStarAtScale_le_barSigmaLimit_of_P4 hP hStruct hP4 n

private theorem barSigmaStarLimit_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    0 < Ch05.Section57.barSigmaStarLimit hP hStruct := by
  exact (Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
    hP hStruct hP4 0).trans_le
      (le_csSup (barSigmaStar_range_bddAbove_of_P4 hP hStruct hP4) ⟨0, rfl⟩)

theorem barSigmaLimit_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    0 < Ch05.Section57.barSigmaLimit hP hStruct :=
  (barSigmaStarLimit_pos_of_P4 hP hStruct hP4).trans_le
    (barSigmaStarLimit_le_barSigmaLimit_of_P4 hP hStruct hP4)

private theorem barSigmaLimit_le_one_add_mul_barSigmaStarLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P)
    {ε : ℝ} (hε : 0 < ε) :
    Ch05.Section57.barSigmaLimit hP hStruct ≤
      (1 + ε) * Ch05.Section57.barSigmaStarLimit hP hStruct := by
  obtain ⟨C, alpha, _hC, ha, hconv⟩ :=
    Ch05.Section51.annealedConvergence_homogenizationScale hP4.params
  let N : ℕ := Ch05.annealedAlgebraicEntryScale P hP4 C
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) < ε :=
    (exponentialDecay_tendsto_zero ha) (Iio_mem_nhds hε)
  rcases eventually_atTop.1 hev with ⟨n, hn⟩
  let m := N + n
  have htheta : Ch05.thetaAtScale hP hStruct (m : ℤ) ≤
      1 + Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) := by
    simpa [N, m] using hconv hP hStruct hP4 rfl n
  have htheta' : Ch05.thetaAtScale hP hStruct (m : ℤ) ≤ 1 + ε := by
    linarith [(hn n le_rfl).le]
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hcm : 0 < cm := by
    simpa [cm] using Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hratio : bm * cm⁻¹ ≤ 1 + ε := by
    simpa [Ch05.thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, bm, cm]
      using htheta'
  have hb : bm ≤ (1 + ε) * cm := by
    have hmul := mul_le_mul_of_nonneg_right hratio hcm.le
    calc
      bm = bm * cm⁻¹ * cm := by field_simp [hcm.ne']
      _ ≤ (1 + ε) * cm := hmul
  calc
    Ch05.Section57.barSigmaLimit hP hStruct ≤ bm :=
      csInf_le (barSigma_range_bddBelow_of_P4 hP hStruct hP4) ⟨m, rfl⟩
    _ ≤ (1 + ε) * cm := hb
    _ ≤ (1 + ε) * Ch05.Section57.barSigmaStarLimit hP hStruct := by
      exact mul_le_mul_of_nonneg_left
        (le_csSup (barSigmaStar_range_bddAbove_of_P4 hP hStruct hP4) ⟨m, rfl⟩)
        (by linarith)

/-- The primal and starred scalar limits coincide under the exact `(P4)`
assumption, without the stronger Section 5.7 quenched-tail record. -/
theorem barSigmaLimit_eq_barSigmaStarLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Ch05.Section57.barSigmaLimit hP hStruct =
      Ch05.Section57.barSigmaStarLimit hP hStruct := by
  refine le_antisymm ?_ (barSigmaStarLimit_le_barSigmaLimit_of_P4 hP hStruct hP4)
  exact le_of_forall_le_one_add_mul
    (barSigmaStarLimit_pos_of_P4 hP hStruct hP4).le
    (fun ε hε => barSigmaLimit_le_one_add_mul_barSigmaStarLimit_of_P4
      hP hStruct hP4 hε)

theorem barSigmaStarAtScale_tendsto_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Tendsto (fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ)) atTop
      (nhds (Ch05.Section57.barSigmaLimit hP hStruct)) := by
  simpa [barSigmaLimit_eq_barSigmaStarLimit_of_P4 hP hStruct hP4] using
    barSigmaStarAtScale_tendsto_barSigmaStarLimit_of_P4 hP hStruct hP4

/-- Under `(P4)`, the honest full annealed block matrices converge entrywise
to the block diagonal with the common scalar limit and its inverse. -/
theorem annealedFullBlockMatrixAtScale_tendsto_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Tendsto
      (fun n : ℕ => toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (n : ℤ)))
      atTop
      (nhds (toFullBlockMat (Ch02.blockDiag
        (Ch05.Section57.barSigmaLimit hP hStruct • (1 : Mat d))
        ((Ch05.Section57.barSigmaLimit hP hStruct)⁻¹ • (1 : Mat d))))) := by
  let L := Ch05.Section57.barSigmaLimit hP hStruct
  have hup : Tendsto (fun n : ℕ => hP.barSigmaAtScale hStruct (n : ℤ))
      atTop (nhds L) := by
    simpa [L] using barSigmaAtScale_tendsto_barSigmaLimit_of_P4 hP hStruct hP4
  have hstar : Tendsto (fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ))
      atTop (nhds L) := by
    simpa [L] using barSigmaStarAtScale_tendsto_barSigmaLimit_of_P4 hP hStruct hP4
  have hstarInv : Tendsto
      (fun n : ℕ => (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹)
      atTop (nhds L⁻¹) :=
    hstar.inv₀ (by exact (barSigmaLimit_pos_of_P4 hP hStruct hP4).ne')
  have hBlock (n : ℕ) : Ch04.annealedBlockMatrixAtScale P (n : ℤ) =
      Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (n : ℤ) :=
    Ch05.Section54.VarianceBoundGoodScale.annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
        hP hStruct (n : ℤ)
  apply tendsto_pi_nhds.mpr
  intro alpha
  apply tendsto_pi_nhds.mpr
  intro beta
  cases alpha with
  | inl i =>
      cases beta with
      | inl j =>
          simpa [L, toFullBlockMat, Ch02.blockDiag,
            Ch04.scalarAnnealedBlockMatrixAtScale, hBlock, Pi.smul_apply] using
            hup.mul_const ((1 : Mat d) i j)
      | inr j =>
          simp [toFullBlockMat, Ch02.blockDiag,
            Ch04.scalarAnnealedBlockMatrixAtScale, hBlock]
  | inr i =>
      cases beta with
      | inl j =>
          simp [toFullBlockMat, Ch02.blockDiag,
            Ch04.scalarAnnealedBlockMatrixAtScale, hBlock]
      | inr j =>
          simpa [L, toFullBlockMat, Ch02.blockDiag,
            Ch04.scalarAnnealedBlockMatrixAtScale, hBlock, Pi.smul_apply] using
            hstarInv.mul_const ((1 : Mat d) i j)

/-- Spatial normalization does not alter the infinite-volume full-block
coefficient. -/
theorem annealedFullBlockMatrixAtScale_tendsto_of_scaleNormalized_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (k : ℕ)
    (hStruct : Ch04.RestrictionStructuralLaw
      (Ch04.restrictionScaleNormalizedLaw k P))
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity
      (Ch04.restrictionScaleNormalizedLaw k P)) :
    Tendsto
      (fun n : ℕ => toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (n : ℤ)))
      atTop
      (nhds (toFullBlockMat (Ch02.blockDiag
        (Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct • (1 : Mat d))
        ((Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct)⁻¹ •
          (1 : Mat d))))) := by
  have hnorm := annealedFullBlockMatrixAtScale_tendsto_barSigmaLimit_of_P4
    (hP.scaleNormalized k) hStruct hP4
  have htail : Tendsto
      (fun n : ℕ => toFullBlockMat
        (Ch04.annealedBlockMatrixAtScale P ((n + k : ℕ) : ℤ))) atTop
      (nhds (toFullBlockMat (Ch02.blockDiag
        (Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct • (1 : Mat d))
        ((Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct)⁻¹ •
          (1 : Mat d))))) := by
    refine hnorm.congr' (Eventually.of_forall fun n => ?_)
    rw [Ch04.annealedBlockMatrixAtScale_restrictionScaleNormalizedLaw hP k n]
    simp only [Nat.add_comm]
  exact (tendsto_add_atTop_iff_nat k).mp htail

end

end SubdiffusiveProcess.CoarseGrainingVocab
