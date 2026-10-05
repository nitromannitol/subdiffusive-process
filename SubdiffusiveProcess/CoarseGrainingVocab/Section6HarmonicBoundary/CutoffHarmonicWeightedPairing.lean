
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventWeightedCutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicFluxAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicH1Circ

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Good-event cutoff pairing with its absorbable fine coefficient `mu` and
coarse `L²` remainder `R` exposed. -/
theorem exists_localBoundaryWeightedCutoffPairingBudget (d : ℕ) [NeZero d] :
    ∃ Cp Cw Bc Bw : ℝ,
      0 < Cp ∧ 0 < Cw ∧ 0 < Bc ∧ 0 < Bw ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        ∀ (g : Vec d → Vec d) (u : ForcedCubeSolution Q A g)
          (w : H1Function (openCubeSet Q))
          (eta : Vec d → ℝ) (Bcut : ℝ) (height : ℕ),
          ForceBesovRegularity Q (s / 3) g →
          ContDiff ℝ (⊤ : ℕ∞) eta → HasCompactSupport eta →
          tsupport eta ⊆ openCubeSet Q → 0 ≤ Bcut →
          MemLp (scalarCutoffGradientField eta) ∞ (normalizedCubeMeasure Q) →
          (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
            (fun q => scalarCutoffGradientField eta q i)) →
          (∀ i : Fin d, ∀ q ∈ cubeSet Q,
            ‖fderiv ℝ (fun p => scalarCutoffGradientField eta p i) q‖ ≤ Bcut) →
          Integrable (fun q =>
            vecDot (forcedSolutionCorrectedFluxField Q A g u q)
              (w.toFun q • scalarCutoffGradientField eta q))
            (normalizedCubeMeasure Q) →
          Integrable (fun q =>
            vecDot (forcedSolutionCorrectedFluxField Q A g u q)
              ((cubeAverage Q w.toFun) • scalarCutoffGradientField eta q))
            (normalizedCubeMeasure Q) →
          let t := s / 3
          let xi := scalarCutoffGradientField eta
          let Ew := cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q A) w.grad)
          let Eu := cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q A) u.toH1.grad)
          let X := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
          let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
          let Kcirc := cubeBesovScaleWeight (-t) Q *
            ((geometricDiscount t 1)⁻¹ * ((d : ℝ) * Real.sqrt (Bc * sigma⁻¹)))
          let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
            ((fullVectorPoincareCubeConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Kcirc))
          let mu := 2 * cubeLpNorm Q ∞ xi *
            boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
          let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
            2 * (cubeScaleFactor Q * Bcut * (Gs * X) +
              cubeLpNorm Q ∞ xi *
                (boundaryFiniteHeightHeadGlobalCoeff t height * X))
          let Afac := Cp * t⁻¹ * (Real.sqrt Bw * Real.sqrt sigma)
          let Gfac :=
            Cp * Real.rpow t (-(5 / 2 : ℝ)) *
                (Real.sqrt Bw * Real.sqrt sigma) *
                (Real.sqrt Bw * Real.sqrt sigma⁻¹) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q t g +
              boundaryNegativeToL2Factor (2 * t) *
                boundaryNormalizedEuclideanL2 Q g
          |cubeAverage Q (fun q =>
            vecDot (forcedSolutionCorrectedFluxField Q A g u q)
              (w.toFun q • xi q))| ≤
            Cp * (Afac * Real.sqrt Eu + Gfac) *
              (mu * Real.sqrt Ew + R) := by
  obtain ⟨Cp, hCp, hpair⟩ :=
    exists_abs_correctedFlux_h1CutoffPairing_weightedFiniteHeight_le d
  obtain ⟨Cw, hCw, hweak⟩ := exists_localBoundaryWeakFluxCap d
  obtain ⟨Bc, hBc, hcirc⟩ := exists_localBoundaryH1CircCaps d
  let Bw := max Bc Cw
  have hBw : 0 < Bw := hBc.trans_le (le_max_left Bc Cw)
  refine ⟨Cp, Cw, Bc, Bw, hCp, hCw, hBc, hBw, ?_⟩
  intro M s hs L m n z x y omega hx hD hgood
  dsimp only
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  intro g u w eta Bcut height hg heta hetaCompact hetaSupport hBcut
    hxiLp hxi hderiv hmain hconst
  let t := s / 3
  let xi := scalarCutoffGradientField eta
  let Ew := cubeAverage Q
    (coefficientEnergyDensity (publicCoeffField Q A) w.grad)
  let Eu := cubeAverage Q
    (coefficientEnergyDensity (publicCoeffField Q A) u.toH1.grad)
  let X := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Kcirc := cubeBesovScaleWeight (-t) Q *
    ((geometricDiscount t 1)⁻¹ * ((d : ℝ) * Real.sqrt (Bc * sigma⁻¹)))
  let Bcirc := Kcirc * Real.sqrt Ew
  let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
    ((fullVectorPoincareCubeConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Kcirc))
  let mu := 2 * cubeLpNorm Q ∞ xi *
    boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
  let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
    2 * (cubeScaleFactor Q * Bcut * (Gs * X) +
      cubeLpNorm Q ∞ xi * (boundaryFiniteHeightHeadGlobalCoeff t height * X))
  let Afac := Cp * t⁻¹ * (Real.sqrt Bw * Real.sqrt sigma)
  let Gfac := Cp * Real.rpow t (-(5 / 2 : ℝ)) *
      (Real.sqrt Bw * Real.sqrt sigma) *
      (Real.sqrt Bw * Real.sqrt sigma⁻¹) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q t g +
    boundaryNegativeToL2Factor (2 * t) * boundaryNormalizedEuclideanL2 Q g
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos
      ((mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1)
      (by norm_num)
  have htHalf : t < 1 / 2 := by dsimp [t]; linarith only [hs.2]
  have hBcirc : 0 ≤ Bcirc := by
    dsimp [Bcirc, Kcirc]
    exact mul_nonneg
      (mul_nonneg (cubeBesovScaleWeight_nonneg (-t) Q)
        (mul_nonneg (inv_nonneg.mpr (geometricDiscount_pos (mul_pos ht (by norm_num))).le)
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))))
      (Real.sqrt_nonneg _)
  have hcirc' : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun q => w.grad q i) ≤ Bcirc := by
    intro i N
    have hraw := hcirc M s hs L m n z x y omega hx hD hgood
      w t (le_refl _) i N
    simpa only [Q, A, sigma, t, Ew, Kcirc, Bcirc, mul_assoc] using hraw
  have hp := hpair (Q := Q) (a := A) (t := t) (g := g) u w
    (eta := eta) (B := Bcut) (Bcirc := Bcirc) height ht htHalf
    (by simpa only [t] using hg) heta hetaCompact hetaSupport hBcut hBcirc
    hxiLp hxi hderiv hcirc' hmain hconst
  dsimp only at hp
  have hweak' := hweak M s hs L m n z x y omega hx hD hgood
    Cp (scaleNormalizedPositiveBesovVectorSeminormTwo Q t g) g u hCp.le
      (by simpa only [t] using hg) le_rfl
  have hBwBc : Cw ≤ Bw := le_max_right _ _
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  have hsqrtB : Real.sqrt Cw ≤ Real.sqrt Bw := Real.sqrt_le_sqrt hBwBc
  have hA : Cp * t⁻¹ * (Real.sqrt Cw * Real.sqrt sigma) ≤ Afac := by
    dsimp [Afac]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsqrtB (Real.sqrt_nonneg _))
      (mul_nonneg hCp.le (inv_nonneg.mpr ht.le))
  have hGfac :
      Cp * Real.rpow t (-(5 / 2 : ℝ)) *
          (Real.sqrt Cw * Real.sqrt sigma) *
          (Real.sqrt Cw * Real.sqrt sigma⁻¹) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q t g +
        boundaryNegativeToL2Factor (2 * t) * boundaryNormalizedEuclideanL2 Q g ≤
      Gfac := by
    dsimp [Gfac]
    have hrootSigma : 0 ≤ Real.sqrt sigma := Real.sqrt_nonneg _
    have hrootInv : 0 ≤ Real.sqrt sigma⁻¹ := Real.sqrt_nonneg _
    have hsemi : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q t g :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (by simpa only [t] using hg)
    gcongr
  have hEu : forcedSolutionEnergyNorm Q A u = Real.sqrt Eu := by
    simpa only [Eu, forcedSolutionGradientField] using
      forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
        Q A u
  rw [hEu] at hweak'
  have hweak'' : weakFluxWithRHSRHS Cp Q A t g u ≤
      Cp * t⁻¹ * (Real.sqrt Cw * Real.sqrt sigma) * Real.sqrt Eu +
        Cp * Real.rpow t (-(5 / 2 : ℝ)) *
          (Real.sqrt Cw * Real.sqrt sigma) *
          (Real.sqrt Cw * Real.sqrt sigma⁻¹) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q t g := by
    simpa only [Q, A, t, sigma] using hweak'
  have hweakSum : weakFluxWithRHSRHS Cp Q A t g u +
        boundaryNegativeToL2Factor (2 * t) * boundaryNormalizedEuclideanL2 Q g ≤
      Afac * Real.sqrt Eu + Gfac := by
    calc
      _ ≤ (Cp * t⁻¹ * (Real.sqrt Cw * Real.sqrt sigma) * Real.sqrt Eu +
            Cp * Real.rpow t (-(5 / 2 : ℝ)) *
              (Real.sqrt Cw * Real.sqrt sigma) *
              (Real.sqrt Cw * Real.sqrt sigma⁻¹) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q t g) +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q g := add_le_add hweak'' le_rfl
      _ = Cp * t⁻¹ * (Real.sqrt Cw * Real.sqrt sigma) * Real.sqrt Eu +
          (Cp * Real.rpow t (-(5 / 2 : ℝ)) *
              (Real.sqrt Cw * Real.sqrt sigma) *
              (Real.sqrt Cw * Real.sqrt sigma⁻¹) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q t g +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q g) := by ring
      _ ≤ Afac * Real.sqrt Eu + Gfac := add_le_add
        (mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)) hGfac
  have hP :
      (d : ℝ) * cubeLpNorm Q ∞ xi * X +
          2 * (cubeScaleFactor Q * Bcut * (Gs * X) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * X +
                boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height *
                  (cubeBesovScaleWeight (-(1 - t)) Q *
                    ((fullVectorPoincareCubeConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                      ((Fintype.card (Fin d) : ℝ) * Bcirc))))) =
        mu * Real.sqrt Ew + R := by
    dsimp [mu, R, Kfine, Bcirc]
    ring
  rw [hP] at hp
  have hPnonneg : 0 ≤ mu * Real.sqrt Ew + R := by
    rw [← hP]
    have hX : 0 ≤ X := by dsimp [X]; exact cubeLpNorm_nonneg Q 2 _
    have hxiNorm : 0 ≤ cubeLpNorm Q ∞ xi := cubeLpNorm_nonneg Q ∞ xi
    have hhead : 0 ≤ boundaryFiniteHeightHeadGlobalCoeff t height :=
      boundaryFiniteHeightHeadGlobalCoeff_nonneg t height
    have htail : 0 ≤ boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height :=
      boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg t (1 - t) height
    have hBr : 0 ≤ cubeBesovScaleWeight (-(1 - t)) Q *
        ((fullVectorPoincareCubeConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc)) :=
      mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) Q)
        (mul_nonneg
          (mul_nonneg (fullVectorPoincareCubeConstant_nonneg Q)
            (Real.rpow_nonneg (by norm_num) _))
          (mul_nonneg (by positivity) hBcirc))
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hxiNorm) hX)
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hBcut)
            (mul_nonneg (Real.sqrt_nonneg _) hX))
          (mul_nonneg hxiNorm
            (add_nonneg (mul_nonneg hhead hX) (mul_nonneg htail hBr)))))
  have hscaled : Cp *
        (weakFluxWithRHSRHS Cp Q A t g u +
          boundaryNegativeToL2Factor (2 * t) * boundaryNormalizedEuclideanL2 Q g) *
        (mu * Real.sqrt Ew + R) ≤
      Cp * (Afac * Real.sqrt Eu + Gfac) * (mu * Real.sqrt Ew + R) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hweakSum hPnonneg) hCp.le
  have hfinal := hp.trans hscaled
  simpa only [Q, A, sigma, t, xi, Ew, Eu, X, Gs, Kcirc, Kfine, mu, R,
    Afac, Gfac] using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
