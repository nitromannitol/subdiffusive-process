module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.FiniteIntegrationClosure

@[expose] public section

/-!
# Finite-corridor closure of the combine expectation display

This module substitutes the completed finite integration chain into the
literal expectation apex.  The bad-event integral remains visible for the
separate probability/Cauchy--Schwarz argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The integrated expectation apex after all matrix variance, annealed-gap,
coordinate-trace, and corridor terms have been discharged. -/
theorem exists_expectedJ_le_varianceClosedDisplay
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ),
        0 < m → L ≤ m - 1 →
        C * Real.rpow 3 (-(3 / 4 : ℝ) * (((m : ℤ) - (L : ℤ) : ℤ) : ℝ)) ≤ 1 / 4 →
        ∀ {m0 : ℕ} {xi delta1 : ℝ}, 2 ≤ xi →
          inductionHypothesis M m0 xi delta1 → L ≤ m0 →
          ∀ p q : Vec d,
            q = ahom M L • p → vecNormSq q ≤ ahom M L →
            expectedJ M L m p q ≤
              C * delta1 *
                (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ))) +
              C * ∑ n ∈ Finset.Icc L m,
                Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                  expectedJDifference M L n m p q +
              2 * ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d in
                  (coarseEllipticityGoodEvent M L m)ᶜ,
                Ch04.restrictionResponseJObservableCubeSet
                  (originCube d ((m : ℤ) - 1)) p q
                  (aCutoffRegCoeffField M L omega) ∂M.P.toMeasure := by
  obtain ⟨C0, hC0, hapex⟩ := exists_expectedJ_le_integrated_preVarianceSplitDisplay d
  let K := finiteIntegrationCorridorConstant d
  let C := max (2 * C0) (2 * C0 * K)
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hK0 : 0 ≤ K := by
    dsimp only [K, finiteIntegrationCorridorConstant,
      finiteIntegrationVarianceConstant]
    positivity
  have hCone : 1 ≤ C := by
    exact hC0.trans (le_trans (by linarith) (le_max_left _ _))
  refine ⟨C, hCone, ?_⟩
  intro M L m hm hLm hsmall m0 xi delta1 hxi hS hLm0 p q hq hqNorm
  have hC0le : C0 ≤ C := by
    exact (by linarith : C0 ≤ 2 * C0).trans (le_max_left _ _)
  have hsmall0 : C0 * Real.rpow 3
      (-(3 / 4 : ℝ) * (((m : ℤ) - (L : ℤ) : ℤ) : ℝ)) ≤ 1 / 4 := by
    have hr : 0 ≤ Real.rpow 3
        (-(3 / 4 : ℝ) * (((m : ℤ) - (L : ℤ) : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    exact (mul_le_mul_of_nonneg_right hC0le hr).trans hsmall
  have hLm' : L ≤ m := by omega
  have hraw := hapex M L m hm hLm hsmall0 p q
  have hmatrix := matrixCorridor_int_add_scaleSeparation_le
    M hxi hS hLm0 hLm' p q hq hqNorm
  let D : ℝ := ∑ n ∈ Finset.Icc L m,
    Real.rpow 3 (-((m - n : ℕ) : ℝ)) * expectedJDifference M L n m p q
  let R : ℝ := delta1 * (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ)))
  let B : ℝ := ∫ omega : Sample d in (coarseEllipticityGoodEvent M L m)ᶜ,
    Ch04.restrictionResponseJObservableCubeSet
      (originCube d ((m : ℤ) - 1)) p q (aCutoffRegCoeffField M L omega)
      ∂M.P.toMeasure
  have hsum :
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
          Real.rpow 3 (-((((m : ℤ) - n : ℤ) : ℤ) : ℝ)) *
            expectedJDifference M L n.toNat m p q = D := by
    simpa only [D] using
      sum_Icc_int_weighted_toNat_eq_sum_Icc_nat_public L m
        (fun n => expectedJDifference M L n m p q)
  have hsumEq :
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
          (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
            expectedJDifference M L n.toNat m p q = D := by
    simpa only using! hsum
  rw [hsumEq] at hraw
  let MV : ℝ := ahom M L *
    ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
      Real.rpow 3 (-(((m : ℤ) - n : ℤ) : ℝ)) *
        ∫ omega,
          descendantsAverage (originCube d (m : ℤ)) (((m : ℤ) - n).toNat)
            (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q) ∂M.P.toMeasure
  let SS : ℝ := ahom M L *
    ∫ omega,
      vecNormSq
        (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
          (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
          (originCube d (m : ℤ)) p q) ∂M.P.toMeasure
  change expectedJ M L m p q ≤
    2 * C0 * D + 2 * C0 * MV + 2 * C0 * SS + 2 * B at hraw
  have hmatrix' : MV + SS ≤ K * R := by
    dsimp only [MV, SS, K, R]
    simpa only [mul_assoc] using hmatrix
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    apply Finset.sum_nonneg
    intro n hn
    have hdiff : 0 ≤ expectedJDifference M L n m p q := by
      rw [expectedJDifference_eq_sub_unconditional]
      exact sub_nonneg.mpr
        (expectedJ_le_of_scale_le M L n m (Finset.mem_Icc.mp hn).2 p q)
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hdiff
  have hdelta : 0 ≤ delta1 := hS.2.1.le
  have hrate : 0 ≤ Real.rpow 3 (-((m - L : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hcoefD : 2 * C0 ≤ C := le_max_left _ _
  have hcoefR : 2 * C0 * K ≤ C := le_max_right _ _
  have hmatScaled := mul_le_mul_of_nonneg_left hmatrix'
    (show 0 ≤ 2 * C0 by positivity)
  have hraw' : expectedJ M L m p q ≤
      2 * C0 * D + 2 * C0 * K * R + 2 * B := by
    ring_nf at hraw hmatScaled ⊢
    nlinarith
  have hDscaled := mul_le_mul_of_nonneg_right hcoefD hD0
  have hRscaled := mul_le_mul_of_nonneg_right hcoefR hR0
  dsimp only [D, R, B] at hraw' ⊢
  nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
