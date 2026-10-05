
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicEllipticityCaps

@[expose] public section

/-!
# Corrected-flux good-event absorption, at a finite cutoff

Cutoff companions of the three good-event theorems of
`Section6HarmonicApproximation.BoundaryGoodEventAbsorption`
(`:125`, `:222`, `:291`): the binder `m ≤ L` is deleted and the good event is
`𝒢^{(L)}_{n+2,z}`.  The single changed leaf is the ellipticity package, taken
from `Section6CutoffHarmonic.exists_localBoundaryEllipticityCaps`.  The two
deterministic ingredients `weakFluxWithRHSRHS_le_of_sixth_caps` and
`halfAbsorb_of_product_budget`, and the corrected-flux pairing estimate
`exists_abs_correctedFlux_pairing_le_weakFlux_mul_positiveBesov`, are good-event
free and are quoted unchanged.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

noncomputable section

variable {d : ℕ} [NeZero d]

/-- On the manuscript good event, the corrected-flux weak RHS on the
translated scale-`n-2` comparison cube has a dimension-only ellipticity
price.  The source norm remains explicit because it is paid later by the v5
inhomogeneous `H^s` hypothesis. -/
theorem exists_localBoundaryWeakFluxCap (d : ℕ) [NeZero d] :
    ∃ B : ℝ, 0 < B ∧
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
        ∀ (C G : ℝ) (g : Vec d → Vec d) (u : ForcedCubeSolution Q A g),
          0 ≤ C → ForceBesovRegularity Q (s / 3) g →
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) g ≤ G →
          weakFluxWithRHSRHS C Q A (s / 3) g u ≤
            C * (s / 3)⁻¹ * (Real.sqrt B * Real.sqrt sigma) *
                forcedSolutionEnergyNorm Q A u +
              C * Real.rpow (s / 3) (-(5 / 2 : ℝ)) *
                (Real.sqrt B * Real.sqrt sigma) *
                (Real.sqrt B * Real.sqrt sigma⁻¹) * G := by
  obtain ⟨E₀, B, hE₀, hB, hcaps⟩ := exists_localBoundaryEllipticityCaps d
  refine ⟨B, hB, ?_⟩
  intro M s hs L m n z x y omega hx hD hgood
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hlocal := hcaps M s hs L m n z x y omega hx hD hgood
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  dsimp only
  intro C G g u hC hg hG
  exact weakFluxWithRHSRHS_le_of_sixth_caps u hC hs0 hsigma hB.le
    hlocal.2.1 hlocal.2.2.1 hg hG

omit [NeZero d] in
/-- Scalar Young step used after the corrected-flux/cutoff-product estimate.
The coefficient `mu` is the fine-scale part of the cutoff budget.  Once its
product with the energy part of the weak flux is at most `1/8`, the two cross
terms spend another `1/8`, leaving the advertised one-quarter absorption. -/
theorem halfAbsorb_of_product_budget
    {pair C A E G P mu R : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hG : 0 ≤ G)
    (hpair : |pair| ≤ C * (A * Real.sqrt E + G) * P)
    (hbudget : P ≤ mu * Real.sqrt E + R)
    (hsmall : C * A * mu ≤ 1 / 8) :
    |pair| ≤
      (1 / 4 : ℝ) * E +
        4 * (C * A * R) ^ 2 + 4 * (C * G * mu) ^ 2 + C * G * R := by
  have hsqrt : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hsqrt_sq : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  have hsum : 0 ≤ A * Real.sqrt E + G :=
    add_nonneg (mul_nonneg hA hsqrt) hG
  have hscaled := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hC hsum)
  have hsmallE : C * A * mu * E ≤ (1 / 8 : ℝ) * E :=
    mul_le_mul_of_nonneg_right hsmall hE
  have hcross1 : C * A * Real.sqrt E * R ≤
      (1 / 16 : ℝ) * E + 4 * (C * A * R) ^ 2 := by
    have hsq : 0 ≤ (Real.sqrt E - 8 * (C * A * R)) ^ 2 := sq_nonneg _
    nlinarith only [hsq, hsqrt_sq]
  have hcross2 : C * G * mu * Real.sqrt E ≤
      (1 / 16 : ℝ) * E + 4 * (C * G * mu) ^ 2 := by
    have hsq : 0 ≤ (Real.sqrt E - 8 * (C * G * mu)) ^ 2 := sq_nonneg _
    nlinarith only [hsq, hsqrt_sq]
  calc
    |pair| ≤ C * (A * Real.sqrt E + G) * P := hpair
    _ ≤ C * (A * Real.sqrt E + G) * (mu * Real.sqrt E + R) := hscaled
    _ = C * A * mu * (Real.sqrt E) ^ 2 + C * A * Real.sqrt E * R +
        C * G * mu * Real.sqrt E + C * G * R := by
      ring
    _ = C * A * mu * E + C * A * Real.sqrt E * R +
        C * G * mu * Real.sqrt E + C * G * R := by rw [hsqrt_sq]
    _ ≤ (1 / 8 : ℝ) * E +
          ((1 / 16 : ℝ) * E + 4 * (C * A * R) ^ 2) +
          ((1 / 16 : ℝ) * E + 4 * (C * G * mu) ^ 2) + C * G * R := by
      linarith only [hsmallE, hcross1, hcross2]
    _ = (1 / 4 : ℝ) * E +
        4 * (C * A * R) ^ 2 + 4 * (C * G * mu) ^ 2 + C * G * R := by ring

/-- The manuscript good event prices the complete corrected-flux factor on
the translated comparison cube.  In particular, no pointwise upper or lower
bound on `aCutoff` occurs in this statement: the coefficient dependence is
entirely through the finite-`2` `LambdaSq`/`lambdaSq` caps supplied by
`Section6CutoffHarmonic.exists_localBoundaryEllipticityCaps`.

The final factor `P` is the positive-Besov size of the cutoff product.  It is
kept visible because the finite-height split of that factor is the place
where the absorbable small coefficient is chosen. -/
theorem exists_localBoundaryCorrectedFluxPairingCap (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
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
        ∀ (g H : Vec d → Vec d) (u : ForcedCubeSolution Q A g) (G P : ℝ),
          ForceBesovRegularity Q (s / 3) g →
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) g ≤ G →
          ForceBesovRegularity Q (s / 3) H → 0 ≤ P →
          scaleNormalizedPositiveBesovVectorNormTwo Q (s / 3) H ≤ P →
          |cubeAverage Q (fun q =>
              vecDot (forcedSolutionCorrectedFluxField Q A g u q) (H q))| ≤
            C *
              (C * (s / 3)⁻¹ * (Real.sqrt B * Real.sqrt sigma) *
                    forcedSolutionEnergyNorm Q A u +
                C * Real.rpow (s / 3) (-(5 / 2 : ℝ)) *
                    (Real.sqrt B * Real.sqrt sigma) *
                    (Real.sqrt B * Real.sqrt sigma⁻¹) * G +
                boundaryNegativeToL2Factor (2 * (s / 3)) *
                    boundaryNormalizedEuclideanL2 Q g) * P := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_abs_correctedFlux_pairing_le_weakFlux_mul_positiveBesov d
  obtain ⟨B, hB, hweak⟩ := exists_localBoundaryWeakFluxCap d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M s hs L m n z x y omega hx hD hgood
  dsimp only
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  intro g H u G P hg hG hH hP hHnorm
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsThird0 : 0 < s / 3 := div_pos hs0 (by norm_num)
  have hsThird1 : s / 3 < 1 := by linarith only [hs.2]
  have hp := hpair (Q := Q) (a := A) (s := s / 3) (g := g) (H := H)
    (B := P) u hsThird0 hsThird1 hg hH hP hHnorm
  have hw := hweak M s hs L m n z x y omega hx hD hgood
    C G g u hC.le hg hG
  have hsum : weakFluxWithRHSRHS C Q A (s / 3) g u +
        boundaryNegativeToL2Factor (2 * (s / 3)) *
          boundaryNormalizedEuclideanL2 Q g ≤
      C * (s / 3)⁻¹ * (Real.sqrt B * Real.sqrt sigma) *
          forcedSolutionEnergyNorm Q A u +
        C * Real.rpow (s / 3) (-(5 / 2 : ℝ)) *
          (Real.sqrt B * Real.sqrt sigma) *
          (Real.sqrt B * Real.sqrt sigma⁻¹) * G +
          boundaryNegativeToL2Factor (2 * (s / 3)) *
          boundaryNormalizedEuclideanL2 Q g :=
    by
      simpa only [Q, A, sigma, add_assoc] using
        add_le_add hw
          (le_refl (boundaryNegativeToL2Factor (2 * (s / 3)) *
            boundaryNormalizedEuclideanL2 Q g))
  exact hp.trans (by
    simpa only [Q, A, sigma, mul_assoc] using
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum hP) hC.le)

/-- Half-absorbable form of the preceding good-event pairing cap.  The
finite-height cutoff split supplies `hbudget`; `hsmall` is then the literal
height-choice obligation.  The conclusion spends exactly one quarter of the
outer energy and leaves only squared coarse-scale/datum remainders. -/
theorem exists_localBoundaryCorrectedFluxPairing_halfAbsorb (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
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
        ∀ (g H : Vec d → Vec d) (u : ForcedCubeSolution Q A g)
          (G P mu R E : ℝ),
          ForceBesovRegularity Q (s / 3) g →
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) g ≤ G →
          ForceBesovRegularity Q (s / 3) H → 0 ≤ P →
          scaleNormalizedPositiveBesovVectorNormTwo Q (s / 3) H ≤ P →
          0 ≤ G → 0 ≤ E →
          forcedSolutionEnergyNorm Q A u = Real.sqrt E →
          P ≤ mu * Real.sqrt E + R →
          C * (C * (s / 3)⁻¹ * (Real.sqrt B * Real.sqrt sigma)) * mu ≤ 1 / 8 →
          |cubeAverage Q (fun q =>
              vecDot (forcedSolutionCorrectedFluxField Q A g u q) (H q))| ≤
            (1 / 4 : ℝ) * E +
              4 * (C * (C * (s / 3)⁻¹ *
                (Real.sqrt B * Real.sqrt sigma)) * R) ^ 2 +
              4 * (C *
                (C * Real.rpow (s / 3) (-(5 / 2 : ℝ)) *
                    (Real.sqrt B * Real.sqrt sigma) *
                    (Real.sqrt B * Real.sqrt sigma⁻¹) * G +
                  boundaryNegativeToL2Factor (2 * (s / 3)) *
                    boundaryNormalizedEuclideanL2 Q g) * mu) ^ 2 +
              C *
                (C * Real.rpow (s / 3) (-(5 / 2 : ℝ)) *
                    (Real.sqrt B * Real.sqrt sigma) *
                    (Real.sqrt B * Real.sqrt sigma⁻¹) * G +
                  boundaryNegativeToL2Factor (2 * (s / 3)) *
                    boundaryNormalizedEuclideanL2 Q g) * R := by
  obtain ⟨C, B, hC, hB, hpair⟩ :=
    exists_localBoundaryCorrectedFluxPairingCap d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M s hs L m n z x y omega hx hD hgood
  dsimp only
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  intro g H u G P mu R E hg hG hH hP hHnorm hG0 hE henergy hbudget hsmall
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hp := hpair M s hs L m n z x y omega hx hD hgood
    (g := g) (H := H) (u := u) (G := G) (P := P) hg hG hH hP hHnorm
  rw [henergy] at hp
  let Afac : ℝ := C * (s / 3)⁻¹ * (Real.sqrt B * Real.sqrt sigma)
  let Gfac : ℝ :=
    C * Real.rpow (s / 3) (-(5 / 2 : ℝ)) *
        (Real.sqrt B * Real.sqrt sigma) *
        (Real.sqrt B * Real.sqrt sigma⁻¹) * G +
      boundaryNegativeToL2Factor (2 * (s / 3)) *
        boundaryNormalizedEuclideanL2 Q g
  have hAfac : 0 ≤ Afac := by
    dsimp [Afac]
    exact mul_nonneg
      (mul_nonneg hC.le (inv_nonneg.mpr (div_nonneg hs0.le (by norm_num))))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hGfac : 0 ≤ Gfac := by
    dsimp [Gfac]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hC.le
              (Real.rpow_nonneg (div_nonneg hs0.le (by norm_num)) _))
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hG0)
      (mul_nonneg (boundaryNegativeToL2Factor_nonneg _)
        (boundaryNormalizedEuclideanL2_nonneg Q g))
  have hp' : |cubeAverage Q (fun q =>
      vecDot (forcedSolutionCorrectedFluxField Q A g u q) (H q))| ≤
      C * (Afac * Real.sqrt E + Gfac) * P := by
    simpa only [Afac, Gfac, add_assoc] using hp
  have hsmall' : C * Afac * mu ≤ 1 / 8 := by
    simpa only [Afac] using hsmall
  simpa only [Afac, Gfac] using
    halfAbsorb_of_product_budget hC.le hAfac hE hGfac hp' hbudget hsmall'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
