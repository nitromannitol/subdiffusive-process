module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CoarseAffineWindowPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.InteriorCellAtScale

@[expose] public section

/-!
# Coarse affine datum price at a free cover scale

This file frees the cube scale in `exists_coarseAffineDirichletLift_goodEvent_energy_le`.
The frozen good event is kept at its scale `n + 2`; descent to a parent of scale `k`
costs the explicit factor `3^((s / 4) (n + 2 - k))`.  The constant outside that
factor depends only on the dimension.

No pointwise upper bound on `aCutoff` is used.  Both parts of the datum are paid
through the coarse finite-`2` and finite-`1` ellipticity quantities.

Argument: `l.harmonic.approximation.good.scales.GMC`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch02 Homogenization.Book.Ch03 MeasureTheory
open Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The good-event coarse affine price on an arbitrary descendant parent.
The displayed power of `3` is the complete cover-depth dependence; the
existential constant is chosen before every model, scale, sample, and datum. -/
theorem exists_coarseAffineDirichletLift_goodEvent_atScale_energy_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ),
        s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L n : ℕ), n + 2 ≤ L →
      ∀ (k : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (y z : Vec d),
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      let Q := originCube d k
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let depth := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)
      ∀ h : H1Function (openCubeSet Q),
        ForceBesovRegularity Q s h.grad →
        ∃ v : DirichletForcedCubeSolution Q A (fun _ ↦ 0),
          v.boundaryData = h ∧
          localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q) v.toH1 ≤
            C * Real.rpow (3 : ℝ) (s / 4 * depth) * sigma *
              (vecNormSq (cubeAverageVec Q h.grad) +
                Real.rpow (s / 2) (-3 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) := by
  obtain ⟨Cdatum, hCdatum, hdatum⟩ :=
    exists_coarseAffineDirichletLift_energy_le d
  obtain ⟨Ctile, hCtile, hcaps⟩ := exists_localTileEllipticityCaps_atScale d
  let K0 : ℝ := 2 * (d : ℝ) * (192 * (d : ℝ) * Ctile ^ 2 + 1)
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hK0 : 0 < K0 := by
    dsimp [K0]
    positivity
  refine ⟨Cdatum * K0, mul_pos hCdatum hK0, ?_⟩
  intro M s hs L n hnL k omega y z hcontain hgood
  dsimp only
  let Q := originCube d k
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let depth : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)
  let B := tileEllipticityConst d Ctile s depth
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hdepth : 0 ≤ depth := by
    dsimp [depth]
    positivity
  have hBpos : 0 < B := by
    dsimp [B]
    exact tileEllipticityConst_pos d Ctile s depth
  obtain ⟨hupperSix, _hlowerSix, _hLambdaHalf, _hLowerThird,
      _hUpperThird, _hTheta⟩ :=
    hcaps M s hs L n hnL k omega y z hcontain hgood
  have hupperFour : sigma⁻¹ * Ch02.LambdaSq Q (s / 4)
      (.finite 2) A ≤ B := by
    have hmono : Ch02.LambdaSq Q (s / 4) (.finite 2) A ≤
        Ch02.LambdaSq Q (s / 6) (.finite 2) A :=
      Ch02.LambdaSq_antitone Q A (by linarith only [hs0])
        (by linarith only [hs0]) (by norm_num)
    exact (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hsigma.le)).trans
      hupperSix
  have hLambda : Ch02.LambdaS Q (s / 2) A ≤ B * sigma :=
    LambdaS_le_of_localRatioCap Q A (by linarith only [hs0]) hsigma
      (by simpa [show s / 2 / 2 = s / 4 by ring] using hupperFour)
  have hBle : B ≤ K0 * Real.rpow (3 : ℝ) (s / 4 * depth) := by
    dsimp [B, K0]
    exact tileEllipticityConst_le d hs0 hdepth
  intro h hreg
  obtain ⟨v, hvDatum, hvEnergy⟩ := hdatum M L
    (translatePotentialSample y omega) Q h hs0 hs.2 hsigma hBpos.le
      hupperSix hLambda hreg
  have hinside : 0 ≤ vecNormSq (cubeAverageVec Q h.grad) +
      Real.rpow (s / 2) (-3 : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2 := by
    exact add_nonneg (vecNormSq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  have hscale : Cdatum * B * sigma ≤
      Cdatum * (K0 * Real.rpow (3 : ℝ) (s / 4 * depth)) * sigma := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBle hCdatum.le) hsigma.le
  refine ⟨v, hvDatum, hvEnergy.trans ?_⟩
  calc
    Cdatum * B * sigma *
        (vecNormSq (cubeAverageVec Q h.grad) +
          Real.rpow (s / 2) (-3 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) ≤
      (Cdatum * (K0 * Real.rpow (3 : ℝ) (s / 4 * depth)) * sigma) *
        (vecNormSq (cubeAverageVec Q h.grad) +
          Real.rpow (s / 2) (-3 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) :=
      mul_le_mul_of_nonneg_right hscale hinside
    _ = Cdatum * K0 * Real.rpow (3 : ℝ) (s / 4 * depth) * sigma *
        (vecNormSq (cubeAverageVec Q h.grad) +
          Real.rpow (s / 2) (-3 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) := by
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
