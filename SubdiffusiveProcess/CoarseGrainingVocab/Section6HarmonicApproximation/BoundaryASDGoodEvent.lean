import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDProjected
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorPrefactorPrice




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- On a projected boundary cell, the amplitude-one good event prices the
entire ASD prefactor and all three ellipticity coefficients.  The only
unpriced object is the datum-centered parent norm itself. -/
theorem exists_projectedBoundaryCellASD_goodEventPrices
    (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        let k : ℤ := (n : ℤ) - 2
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample c omega)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        ∃ g0 : Vec d → Vec d,
          ∃ u0 h0 : H1Function (openCubeSet Q),
            (∀ y, g0 y = g (y + c)) ∧
            (∀ y, u0.toFun y = u.toFun (y + c)) ∧
            (∀ y, u0.grad y = u.grad (y + c)) ∧
            (∀ y, h0.toFun y = h.toFun (y + c)) ∧
            (∀ y, h0.grad y = h.grad (y + c)) ∧
            localizedCoeffEnergyValue
                (caccioppoliCoreSet Q (q - c)) (A.coeffOn Q) u0 ≤
              ((4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ)) *
                (B * sigma *
                    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                    normalizedL2SqOnSet (openCubeSet Q) (fun y ↦
                      u0.toFun y - volumeAverage (openCubeSet Q) h0.toFun) +
                  Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
                      (fun y ↦ -g0 y) ^ 2 +
                  Real.rpow (sOrder.1 / 2) (-3 : ℝ) * (B * sigma) *
                    scaleNormalizedPositiveBesovVectorNormTwo Q sOrder.1
                      h0.grad ^ 2) := by
  obtain ⟨C, hC, hASD⟩ := exists_projectedBoundaryCellASD d
  obtain ⟨_E, B, _hE, hB, hcaps⟩ :=
    exists_localBoundaryEllipticityCaps_nextWindow d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M sOrder hs L m n hmL hnm z x q omega hx hq hgood u h g hdir hg hh
  dsimp only
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hnL : n + 2 ≤ L := by omega
  have hqDomain : q ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 1) x hq
  obtain ⟨g0, u0, h0, hg0, hu0, hu0grad, hh0, hh0grad, hraw⟩ :=
    hASD M L omega m k q sOrder u h g hdir hg hh hs.2 hkm hqDomain
  have hPsub : translatedCube d k c ⊆
      truncatedCube d (m : ℤ) (n : ℤ) x :=
    translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k] using hq) hkm
  have hcU : c ∈ truncatedCube d (m : ℤ) (n : ℤ) x := hPsub (by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    simpa using Section6ExcessDecay.zero_mem_cube d k)
  have hcap := hcaps M sOrder.1 hs L m n hnL z x c omega hx hcU hgood
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hhalf := interiorHalfEllipticityCaps_of_sixth Q A hs0 hsigma
    hcap.2.2.2.1 hcap.2.2.1
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := A) hC hs0 hs.2 hhalf.2.2
  have hupper4 : sigma⁻¹ * Ch02.LambdaSq Q (sOrder.1 / 4)
      (.finite 2) A ≤ B := by
    have hmono : Ch02.LambdaSq Q (sOrder.1 / 4) (.finite 2) A ≤
        Ch02.LambdaSq Q (sOrder.1 / 6) (.finite 2) A :=
      Ch02.LambdaSq_antitone Q A (by linarith only [hs0])
        (by linarith only [hs0]) (by norm_num)
    exact (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hsigma.le)).trans
      hcap.2.1
  have hLam : Ch02.LambdaS Q (sOrder.1 / 2) A ≤ B * sigma :=
    LambdaS_le_of_localRatioCap Q A (by linarith only [hs0]) hsigma
      (by simpa [show sOrder.1 / 2 / 2 = sOrder.1 / 4 by ring] using hupper4)
  let X : ℝ := Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
    normalizedL2SqOnSet (openCubeSet Q) (fun y ↦
      u0.toFun y - volumeAverage (openCubeSet Q) h0.toFun)
  let F : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
    (fun y ↦ -g0 y) ^ 2
  let H : ℝ := scaleNormalizedPositiveBesovVectorNormTwo Q sOrder.1 h0.grad ^ 2
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  have hF0 : 0 ≤ F := sq_nonneg _
  have hH0 : 0 ≤ H := sq_nonneg _
  have hforceCoef0 : 0 ≤ Real.rpow (sOrder.1 / 2) (-11 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hdatumCoef0 : 0 ≤ Real.rpow (sOrder.1 / 2) (-3 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hlamInvR :
      Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
        B * sigma⁻¹ := by
    exact (Real.rpow_neg_one _).trans_le hhalf.1
  have hinner :
      Ch02.lambdaS Q (sOrder.1 / 2) A * X +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
              Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) * F +
          Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
              Ch02.LambdaS Q (sOrder.1 / 2) A * H ≤
        B * sigma * X +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) * F +
          Real.rpow (sOrder.1 / 2) (-3 : ℝ) * (B * sigma) * H := by
    exact add_le_add
      (add_le_add
        (mul_le_mul_of_nonneg_right hhalf.2.1 hX0)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlamInvR hforceCoef0) hF0))
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLam hdatumCoef0) hH0)
  have hinner0 : 0 ≤
      Ch02.lambdaS Q (sOrder.1 / 2) A * X +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
              Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) * F +
              Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
              Ch02.LambdaS Q (sOrder.1 / 2) A * H := by
    have hlam0 : 0 ≤ Ch02.lambdaS Q (sOrder.1 / 2) A := by
      rw [Ch02.lambdaS]
      exact Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs0]) (by norm_num)
    have hLam0 : 0 ≤ Ch02.LambdaS Q (sOrder.1 / 2) A := by
      rw [Ch02.LambdaS]
      exact Ch02.LambdaSq_finite_nonneg Q A (by linarith only [hs0]) (by norm_num)
    exact add_nonneg
      (add_nonneg (mul_nonneg hlam0 hX0)
        (mul_nonneg
          (mul_nonneg hforceCoef0 (Real.rpow_nonneg hlam0 _)) hF0))
      (mul_nonneg (mul_nonneg hdatumCoef0 hLam0) hH0)
  have hpriced := mul_le_mul hpref hinner hinner0 (by positivity)
  refine ⟨g0, u0, h0, hg0, hu0, hu0grad, hh0, hh0grad, ?_⟩
  apply hraw.trans
  simpa only [Q, A, sigma, X, F, H, mul_assoc] using hpriced

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
