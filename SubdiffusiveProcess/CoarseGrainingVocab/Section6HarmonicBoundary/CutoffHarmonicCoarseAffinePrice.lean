
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CoarseAffineGoodEventPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicEllipticityCaps

@[expose] public section

/-!
# Good-event coarse affine datum price, at a finite cutoff

Cutoff companion of
`Section6HarmonicBoundary.exists_coarseAffineDirichletLift_goodEvent_energy_le`:
the binder `n + 2 ≤ L` is deleted and the good event is `𝒢^{(L)}_{n+2,z}`.  The
single changed leaf is the ellipticity package
`Section6HolderBelowCutoff.exists_localCutoffEllipticityCaps_nextWindow`; the
coarse affine separation is deterministic and is quoted unchanged.

Argument: `l.harmonic.approximation.good.scales.GMC`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch02 Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

noncomputable section

variable {d : ℕ} [NeZero d]

/-- On the frozen good event, the harmonic lift of a projected boundary datum
is controlled by its coarse mean slope and its centered positive-Besov
seminorm, with one dimension-only constant. -/
theorem exists_coarseAffineDirichletLift_goodEvent_energy_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ),
        s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ),
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        y ∈ truncatedCube d (m : ℤ) (n : ℤ) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      ∀ h : H1Function (openCubeSet Q),
        ForceBesovRegularity Q s h.grad →
        ∃ v : DirichletForcedCubeSolution Q A (fun _ ↦ 0),
          v.boundaryData = h ∧
          localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q) v.toH1 ≤
            C * sigma *
              (vecNormSq (cubeAverageVec Q h.grad) +
                Real.rpow (s / 2) (-3 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) := by
  obtain ⟨Cdatum, hCdatum, hdatum⟩ := exists_coarseAffineDirichletLift_energy_le d
  obtain ⟨_E, B, _hE, hB, hcaps⟩ :=
    exists_localCutoffEllipticityCaps_nextWindow d
  refine ⟨Cdatum * B, mul_pos hCdatum hB, ?_⟩
  intro M s hs L m n z x y omega hx hy hgood
  dsimp only
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hcap := hcaps M s hs L m n z x y omega hx hy hgood
  have hupperFour : sigma⁻¹ * Ch02.LambdaSq Q (s / 4)
      (.finite 2) A ≤ B := by
    have hmono : Ch02.LambdaSq Q (s / 4) (.finite 2) A ≤
        Ch02.LambdaSq Q (s / 6) (.finite 2) A :=
      Ch02.LambdaSq_antitone Q A (by linarith only [hs0])
        (by linarith only [hs0]) (by norm_num)
    exact (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hsigma.le)).trans
      hcap.2.1
  have hLambda : Ch02.LambdaS Q (s / 2) A ≤ B * sigma :=
    LambdaS_le_of_localRatioCap Q A (by linarith only [hs0]) hsigma
      (by simpa [show s / 2 / 2 = s / 4 by ring] using hupperFour)
  intro h hreg
  have hresult := hdatum M L (translatePotentialSample y omega) Q h
    hs0 hs.2 hsigma hB.le hcap.2.1 hLambda hreg
  simpa only [Q, A, sigma, mul_assoc] using hresult

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
