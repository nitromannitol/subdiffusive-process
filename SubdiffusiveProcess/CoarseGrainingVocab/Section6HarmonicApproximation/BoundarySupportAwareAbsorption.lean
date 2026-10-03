module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySupportAwareProduct
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventWeightedCutoff

@[expose] public section

/-!
# Half absorption for the support-safe boundary product

This module performs the Young step after the uncentered finite-height
product.  It is independent of the later finite descendant averaging: the
caller supplies the local weak-flux price and the coefficient-energy split.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The support-free finite-height product, with its fine term absorbed into
one quarter of the local solution energy.  The displayed remainder is exactly
the input of `descendantsAverage_twoEnergyYoungRemainder_le`. -/
theorem exists_abs_boundaryCorrectedFluxDensity_weightedFiniteHeight_quarter
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {t : ℝ} {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (w : H1Function (openCubeSet Q))
        {eta : Vec d → ℝ} {B Bcirc Kcirc A G Eu Eh Ew : ℝ} (height : ℕ),
        0 < t → t < 1 / 2 →
        ForceBesovRegularity Q t (fun x ↦ -g₀ x) →
        0 ≤ B → 0 ≤ Bcirc → 0 ≤ Kcirc → 0 ≤ A → 0 ≤ G →
        0 ≤ Eu → 0 ≤ Eh →
        MemLp (scalarCutoffGradientField (fun y ↦ eta y ^ 2)) ∞
          (normalizedCubeMeasure Q) →
        (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i)) →
        (∀ i : Fin d, ∀ z ∈ cubeSet Q,
          ‖fderiv ℝ
              (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i) z‖ ≤ B) →
        (∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x ↦ w.grad x i) ≤ Bcirc) →
        Bcirc = Kcirc * Real.sqrt Ew →
        cubeAverage Q
            (coefficientEnergyDensity
              (publicCoeffField Q (aCutoffFamily M L omega)) u.toH1.grad) = Eu →
        cubeAverage Q
            (coefficientEnergyDensity
              (publicCoeffField Q (aCutoffFamily M L omega)) w.grad) = Ew →
        Ew ≤ 2 * Eu + 2 * Eh →
        weakFluxWithRHSRHS C Q (aCutoffFamily M L omega) t
              (fun x ↦ -g₀ x) u +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q (fun x ↦ -g₀ x) ≤
          A * Real.sqrt Eu + G →
        let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
        let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
        let Cfull := fullVectorPoincareCubeConstant Q
        let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
          ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Kcirc))
        let X₀ := cubeLpNorm Q (2 : ℝ≥0∞) w.toFun
        let Xc := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
        let mu := 2 * cubeLpNorm Q ∞ xi *
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
        let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
          2 * (cubeScaleFactor Q * B * (Gs * X₀) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
        C * A * (Real.sqrt 2 * mu) ≤ 1 / 8 →
        |cubeAverage Q
            (boundaryCorrectedFluxCutoffPairingDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
              w.toFun u.toH1.grad g₀)| ≤
          (1 / 4 : ℝ) * Eu +
            4 * (C * A * (Real.sqrt 2 * mu * Real.sqrt Eh + R)) ^ 2 +
            4 * (C * G * (Real.sqrt 2 * mu)) ^ 2 +
              C * G * (Real.sqrt 2 * mu * Real.sqrt Eh + R) := by
  obtain ⟨C, hC, hproduct⟩ :=
    exists_abs_boundaryCorrectedFluxDensity_weightedFiniteHeight_le d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q t g₀ u w eta B Bcirc Kcirc A G Eu Eh Ew height
    ht htHalf hg hB hBcirc hKcirc hA hG hEu hEh hxiLp hxi hderiv hcirc
    hBcircEq hEuEq hEwEq hsplit hweak
  dsimp only
  let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Cfull := fullVectorPoincareCubeConstant Q
  let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
    ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Kcirc))
  let X₀ := cubeLpNorm Q (2 : ℝ≥0∞) w.toFun
  let Xc := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
  let mu := 2 * cubeLpNorm Q ∞ xi *
    boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
  let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
    2 * (cubeScaleFactor Q * B * (Gs * X₀) +
      cubeLpNorm Q ∞ xi *
        (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
  intro hsmall
  have hraw := hproduct M L omega u w (eta := eta) (B := B)
    (Bcirc := Bcirc) height ht htHalf hg hB hBcirc hxiLp hxi hderiv hcirc
  dsimp only at hraw
  have hP :
      (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
          2 * (cubeScaleFactor Q * B * (Gs * X₀) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * Xc +
                boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height *
                  (cubeBesovScaleWeight (-(1 - t)) Q *
                    ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                      ((Fintype.card (Fin d) : ℝ) * Bcirc))))) =
        mu * Real.sqrt Ew + R := by
    dsimp [mu, R, Kfine]
    rw [hBcircEq]
    ring
  rw [hP] at hraw
  have hKfine : 0 ≤ Kfine := by
    dsimp [Kfine, Cfull]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) Q)
      (mul_nonneg
        (mul_nonneg (fullVectorPoincareCubeConstant_nonneg Q)
          (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg (by positivity) hKcirc))
  have hmu : 0 ≤ mu := by
    dsimp only [mu]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (cubeLpNorm_nonneg Q ∞ xi))
        (boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg t (1 - t) height))
      hKfine
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (cubeLpNorm_nonneg Q ∞ xi))
        (cubeLpNorm_nonneg Q 2 w.toFun))
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
            (mul_nonneg (Real.sqrt_nonneg _)
              (cubeLpNorm_nonneg Q 2 w.toFun)))
          (mul_nonneg (cubeLpNorm_nonneg Q ∞ xi)
            (mul_nonneg
              (boundaryFiniteHeightHeadGlobalCoeff_nonneg t height)
              (cubeLpNorm_nonneg Q 2 (cubeFluctuation Q w.toFun))))))
  have hbudget : 0 ≤ mu * Real.sqrt Ew + R :=
    add_nonneg (mul_nonneg hmu (Real.sqrt_nonneg _)) hR
  have hscaled :
      C * (weakFluxWithRHSRHS C Q (aCutoffFamily M L omega) t
              (fun x ↦ -g₀ x) u +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q (fun x ↦ -g₀ x)) *
          (mu * Real.sqrt Ew + R) ≤
        C * (A * Real.sqrt Eu + G) * (mu * Real.sqrt Ew + R) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hweak hbudget) hC.le
  have hpair : |cubeAverage Q
      (boundaryCorrectedFluxCutoffPairingDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
        w.toFun u.toH1.grad g₀)| ≤
      C * (A * Real.sqrt Eu + G) * (mu * Real.sqrt Ew + R) :=
    hraw.trans hscaled
  have hquarter := halfAbsorb_of_twoEnergy_product_budget
    hC.le hA hEu hEh hG hmu hpair hsplit hsmall
  simpa only [xi, Gs, Cfull, Kfine, X₀, Xc, mu, R] using hquarter

/-- The support-free product for the combined signed flux.  Its flux energy
and value-factor energy have distinct decompositions, exactly as in the
affine/residual boundary split. -/
theorem exists_abs_boundaryCorrectedFluxDensity_weightedFiniteHeight_combined
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {t : ℝ} {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (w : H1Function (openCubeSet Q))
        {eta : Vec d → ℝ} {B Bcirc Kcirc A G Er Ev Eh : ℝ} (height : ℕ),
        0 < t → t < 1 / 2 →
        ForceBesovRegularity Q t (fun x ↦ -g₀ x) →
        0 ≤ B → 0 ≤ Bcirc → 0 ≤ Kcirc → 0 ≤ A → 0 ≤ G →
        0 ≤ Er → 0 ≤ Ev → 0 ≤ Eh →
        MemLp (scalarCutoffGradientField (fun y ↦ eta y ^ 2)) ∞
          (normalizedCubeMeasure Q) →
        (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i)) →
        (∀ i : Fin d, ∀ z ∈ cubeSet Q,
          ‖fderiv ℝ
              (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i) z‖ ≤ B) →
        (∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x ↦ w.grad x i) ≤ Bcirc) →
        let Ecomb := cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) u.toH1.grad)
        let Ew := cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) w.grad)
        Bcirc = Kcirc * Real.sqrt Ew →
        Ecomb ≤ 2 * Er + 8 * Ev →
        Ew ≤ 2 * Er + 2 * Eh →
        weakFluxWithRHSRHS C Q (aCutoffFamily M L omega) t
              (fun x ↦ -g₀ x) u +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q (fun x ↦ -g₀ x) ≤
          A * Real.sqrt Ecomb + G →
        let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
        let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
        let Cfull := fullVectorPoincareCubeConstant Q
        let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
          ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Kcirc))
        let X₀ := cubeLpNorm Q (2 : ℝ≥0∞) w.toFun
        let Xc := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
        let mu := 2 * cubeLpNorm Q ∞ xi *
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
        let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
          2 * (cubeScaleFactor Q * B * (Gs * X₀) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
        C * A * (Real.sqrt 2 * mu) ≤ 1 / 8 →
        |cubeAverage Q
            (boundaryCorrectedFluxCutoffPairingDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
              w.toFun u.toH1.grad g₀)| ≤
          (1 / 4 : ℝ) * Er + (1 / 2 : ℝ) * Ev +
            (1 / 8 : ℝ) * Eh +
            16 * (C * A * R) ^ 2 + 16 * (C * G * mu) ^ 2 + C * G * R := by
  obtain ⟨C, hC, hproduct⟩ :=
    exists_abs_boundaryCorrectedFluxDensity_weightedFiniteHeight_le d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q t g₀ u w eta B Bcirc Kcirc A G Er Ev Eh height
    ht htHalf hg hB hBcirc hKcirc hA hG hEr hEv hEh hxiLp hxi hderiv hcirc
  dsimp only
  let Ecomb := cubeAverage Q
    (coefficientEnergyDensity
      (publicCoeffField Q (aCutoffFamily M L omega)) u.toH1.grad)
  let Ew := cubeAverage Q
    (coefficientEnergyDensity
      (publicCoeffField Q (aCutoffFamily M L omega)) w.grad)
  intro hBcircEq hcomb hvalue hweak
  let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Cfull := fullVectorPoincareCubeConstant Q
  let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
    ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Kcirc))
  let X₀ := cubeLpNorm Q (2 : ℝ≥0∞) w.toFun
  let Xc := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
  let mu := 2 * cubeLpNorm Q ∞ xi *
    boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
  let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
    2 * (cubeScaleFactor Q * B * (Gs * X₀) +
      cubeLpNorm Q ∞ xi *
        (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
  intro hsmall
  have hraw := hproduct M L omega u w (eta := eta) (B := B)
    (Bcirc := Bcirc) height ht htHalf hg hB hBcirc hxiLp hxi hderiv hcirc
  dsimp only at hraw
  have hP :
      (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
          2 * (cubeScaleFactor Q * B * (Gs * X₀) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * Xc +
                boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height *
                  (cubeBesovScaleWeight (-(1 - t)) Q *
                    ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                      ((Fintype.card (Fin d) : ℝ) * Bcirc))))) =
        mu * Real.sqrt Ew + R := by
    dsimp [mu, R, Kfine]
    rw [hBcircEq]
    ring
  rw [hP] at hraw
  have hKfine : 0 ≤ Kfine := by
    dsimp [Kfine, Cfull]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) Q)
      (mul_nonneg
        (mul_nonneg (fullVectorPoincareCubeConstant_nonneg Q)
          (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg (by positivity) hKcirc))
  have hmu : 0 ≤ mu := by
    dsimp only [mu]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (cubeLpNorm_nonneg Q ∞ xi))
        (boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg t (1 - t) height))
      hKfine
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (cubeLpNorm_nonneg Q ∞ xi))
        (cubeLpNorm_nonneg Q 2 w.toFun))
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
            (mul_nonneg (Real.sqrt_nonneg _)
              (cubeLpNorm_nonneg Q 2 w.toFun)))
          (mul_nonneg (cubeLpNorm_nonneg Q ∞ xi)
            (mul_nonneg
              (boundaryFiniteHeightHeadGlobalCoeff_nonneg t height)
              (cubeLpNorm_nonneg Q 2 (cubeFluctuation Q w.toFun))))))
  have hbudget : 0 ≤ mu * Real.sqrt Ew + R :=
    add_nonneg (mul_nonneg hmu (Real.sqrt_nonneg _)) hR
  have hscaled :
      C * (weakFluxWithRHSRHS C Q (aCutoffFamily M L omega) t
              (fun x ↦ -g₀ x) u +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q (fun x ↦ -g₀ x)) *
          (mu * Real.sqrt Ew + R) ≤
        C * (A * Real.sqrt Ecomb + G) * (mu * Real.sqrt Ew + R) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hweak hbudget) hC.le
  have hpair : |cubeAverage Q
      (boundaryCorrectedFluxCutoffPairingDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
        w.toFun u.toH1.grad g₀)| ≤
      C * (A * Real.sqrt Ecomb + G) * (mu * Real.sqrt Ew + R) :=
    hraw.trans hscaled
  have hEcomb : 0 ≤ Ecomb := by
    dsimp [Ecomb]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) u.toH1.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hEw : 0 ≤ Ew := by
    dsimp [Ew]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) w.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hcombined := quarterResidualAbsorb_of_combinedFlux_product_budget
    hC.le hA hEcomb hEw hmu hpair hcomb hvalue hsmall
  simpa only [xi, Gs, Cfull, Kfine, X₀, Xc, mu, R] using hcombined

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
