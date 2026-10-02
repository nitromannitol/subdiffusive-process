/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CoarseAffineWindowPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicCoarseAffinePrice




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The good-event harmonic datum competitor, priced by the ambient window
mean and an explicit fractional-seminorm budget.  In particular, the factor
`(s / 2)⁻³` multiplies only the centered positive-Besov seminorm price. -/
theorem exists_coarseAffineDirichletLift_window_energy_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : FractionalOrder),
        s.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), 
      ∀ (z x c : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        c ∈ truncatedCube d (m : ℤ) (n : ℤ) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s.1 / 8) →
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample c omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      ∀ (U : Set (Vec d)) (D : ℝ)
        (h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (h0 : H1Function (openCubeSet Q)),
        (∀ y, h0.grad y = h.grad (y + c)) →
        Ch03.ABK26.MemCubeEuclideanFullWsp
          Q s FiniteLpExponent.two h0.grad →
        translateSet c (openCubeSet Q) ⊆ U →
        U ⊆ openCubeSet (originCube d (m : ℤ)) →
        MeasurableSet U → 0 < volume U → volume U ≠ ∞ →
        0 < (volume (translateSet c (openCubeSet Q))).toReal →
        (∀ y ∈ U, ∀ y' ∈ U, euclideanNorm (y - y') ≤ D) →
        fractionalSeminormOn U s.1 h.grad ≠ ∞ →
        ∃ v : DirichletForcedCubeSolution Q A (fun _ ↦ 0),
          v.boundaryData = h0 ∧
          localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q) v.toH1 ≤
            C * sigma *
              (vecNormSq (averageVecOn U h.grad) +
                (Real.sqrt ((volume U).toReal /
                    (volume (translateSet c (openCubeSet Q))).toReal) *
                  (D ^ (s.1 + (d : ℝ) / 2) *
                    Real.rpow s.1 (-(1 / 2 : ℝ)) *
                    (volume U).toReal ^ (-(1 / 2 : ℝ)) *
                    (fractionalSeminormOn U s.1 h.grad).toReal)) ^ 2 +
                Real.rpow (s.1 / 2) (-3 : ℝ) *
                  (caccioppoliExactDatumConstant d *
                    cubeBesovScaleWeight (-s.1) Q *
                    (Real.rpow s.1 (-(1 / 2 : ℝ)) *
                      (Real.sqrt ((volume U).toReal /
                          (volume (translateSet c (openCubeSet Q))).toReal) *
                        (fractionalSeminormOn U s.1 h.grad).toReal))) ^ 2) := by
  obtain ⟨C, hC, hgoodPrice⟩ := exists_coarseAffineDirichletLift_goodEvent_energy_le d
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro M s hs L m n z x c omega hx hc hgood
  dsimp only
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample c omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  intro U D h h0 hh0grad hh0Wsp hPsub hUsub hUmeas hU0 hUtop hPpos hdiam hfrac
  have hgradEq : h0.grad = fun y ↦ h.grad (y + c) := funext hh0grad
  have hreg : ForceBesovRegularity Q s.1 h0.grad :=
    forceBesovRegularity_of_memCubeEuclideanFullWsp_of_exponent_le hh0Wsp le_rfl
  obtain ⟨v, hvDatum, hvEnergy⟩ :=
    hgoodPrice M s.1 hs L m n z x c omega hx hc hgood h0 hreg
  let P := translateSet c (openCubeSet Q)
  let R := Real.sqrt ((volume U).toReal / (volume P).toReal)
  let F := (fractionalSeminormOn U s.1 h.grad).toReal
  let MeanFrac := R * (D ^ (s.1 + (d : ℝ) / 2) *
    Real.rpow s.1 (-(1 / 2 : ℝ)) *
    (volume U).toReal ^ (-(1 / 2 : ℝ)) * F)
  let SemiFrac := caccioppoliExactDatumConstant d *
    cubeBesovScaleWeight (-s.1) Q *
    (Real.rpow s.1 (-(1 / 2 : ℝ)) * (R * F))
  have hUreal : 0 < (volume U).toReal := ENNReal.toReal_pos hU0.ne' hUtop
  have hP0 : volume P ≠ 0 := (ENNReal.toReal_ne_zero.mp hPpos.ne').1
  have hPtop : volume P ≠ ∞ := (ENNReal.toReal_ne_zero.mp hPpos.ne').2
  have hhU : MemLp (fun y ↦ HilbertVec.ofVec (h.grad y)) 2
      (volume.restrict U) :=
    (memHilbertVectorL2_hilbertifyVecField h.grad_memVectorL2).mono_measure
      (Measure.restrict_mono_set volume hUsub)
  have hhP : MemLp (fun y ↦ HilbertVec.ofVec (h.grad y)) 2
      (volume.restrict P) :=
    hhU.mono_measure (Measure.restrict_mono hPsub le_rfl)
  have hmeanLocal := euclideanNorm_averageVecOn_le_vectorNormalizedL2On hPpos hhP
  have hlocal := vectorNormalizedL2On_subwindow_le_mean_add_fractional
    hPsub hUmeas hU0 hUtop hPpos s.2.1 hdiam hhU hfrac
  have hmean : euclideanNorm (cubeAverageVec Q h0.grad) ≤
      MeanFrac + euclideanNorm (averageVecOn U h.grad) := by
    rw [hgradEq, cubeAverageVec_comp_add_eq_averageVecOn_translateSet]
    change euclideanNorm (averageVecOn P h.grad) ≤ _
    exact hmeanLocal.trans (by simpa only [P, R, F, MeanFrac] using hlocal)
  have hmeanSq : vecNormSq (cubeAverageVec Q h0.grad) ≤
      2 * (MeanFrac ^ 2 + vecNormSq (averageVecOn U h.grad)) := by
    rw [← euclideanNorm_sq, ← euclideanNorm_sq]
    have hsquare := pow_le_pow_left₀ (euclideanNorm_nonneg _) hmean 2
    have hquad : (MeanFrac + euclideanNorm (averageVecOn U h.grad)) ^ 2 ≤
        2 * (MeanFrac ^ 2 + euclideanNorm (averageVecOn U h.grad) ^ 2) := by
      nlinarith [sq_nonneg (MeanFrac - euclideanNorm (averageVecOn U h.grad))]
    exact hsquare.trans hquad
  have hh0Wsp' : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two (fun y ↦ h.grad (y + c)) := by
    rwa [← hgradEq]
  have hsemiRaw := scaleNormalizedPositiveBesovVectorSeminormTwo_translate_le_window
    Q c U s h.grad hh0Wsp' hPsub hP0 hPtop hU0.ne' hUtop hfrac
  have hsemi : scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 h0.grad ≤
      SemiFrac := by
    rw [hgradEq]
    simpa only [P, R, F, SemiFrac] using hsemiRaw
  have hsemi0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 h0.grad :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hreg
  have hsemiSq :
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 h0.grad ^ 2 ≤
        SemiFrac ^ 2 :=
    pow_le_pow_left₀ hsemi0 hsemi 2
  have hsigma : 0 ≤ sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact (tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)).le
  have hpow : 0 ≤ Real.rpow (s.1 / 2) (-3 : ℝ) :=
    Real.rpow_nonneg (by linarith only [s.2.1]) _
  have hsemiTerm0 : 0 ≤ Real.rpow (s.1 / 2) (-3 : ℝ) * SemiFrac ^ 2 :=
    mul_nonneg hpow (sq_nonneg _)
  refine ⟨v, hvDatum, hvEnergy.trans ?_⟩
  have hinside :
      vecNormSq (cubeAverageVec Q h0.grad) +
          Real.rpow (s.1 / 2) (-3 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 h0.grad ^ 2 ≤
        2 * (vecNormSq (averageVecOn U h.grad) + MeanFrac ^ 2 +
          Real.rpow (s.1 / 2) (-3 : ℝ) * SemiFrac ^ 2) := by
    calc
      _ ≤ 2 * (MeanFrac ^ 2 + vecNormSq (averageVecOn U h.grad)) +
          Real.rpow (s.1 / 2) (-3 : ℝ) * SemiFrac ^ 2 :=
        add_le_add hmeanSq (mul_le_mul_of_nonneg_left hsemiSq hpow)
      _ ≤ 2 * (vecNormSq (averageVecOn U h.grad) + MeanFrac ^ 2 +
          Real.rpow (s.1 / 2) (-3 : ℝ) * SemiFrac ^ 2) := by
        linarith only [hsemiTerm0]
  have hcoef0 : 0 ≤ C * sigma := mul_nonneg hC.le hsigma
  have hscaled := mul_le_mul_of_nonneg_left hinside hcoef0
  dsimp only [Q, A, sigma, P, R, F, MeanFrac, SemiFrac] at hscaled ⊢
  convert hscaled using 1
  all_goals ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
