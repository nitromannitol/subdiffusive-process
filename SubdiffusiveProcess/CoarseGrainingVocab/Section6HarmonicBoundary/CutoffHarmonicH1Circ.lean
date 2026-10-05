
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryArbitraryH1Circ
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicEllipticityCaps

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- On the manuscript good event, the nonzero-boundary scalar factor has the
two (and indeed all) larger-exponent `circ` controls needed by the full-dual
cutoff-product estimate.  The only coefficient price is
`sqrt (B * sigma⁻¹)`, where `B` is dimension-only. -/
theorem exists_localBoundaryH1CircCaps (d : ℕ) [NeZero d] :
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
        ∀ (u : H1Function (openCubeSet Q)) (r : ℝ), s / 3 ≤ r →
          ∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun q => u.grad q i) ≤
            (cubeBesovScaleWeight (-r) Q *
              ((geometricDiscount r 1)⁻¹ *
                ((d : ℝ) * Real.sqrt (B * sigma⁻¹)))) *
              Real.sqrt (cubeAverage Q
                (coefficientEnergyDensity (publicCoeffField Q A) u.grad)) := by
  obtain ⟨E₀, B, hE₀, hB, hcaps⟩ := exists_localBoundaryEllipticityCaps d
  refine ⟨B, hB, ?_⟩
  intro M s hs L m n z x y omega hx hD hgood
  dsimp only
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hlocal := hcaps M s hs L m n z x y omega hx hD hgood
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  intro u r hsr i N
  have hraw := aCutoff_h1Gradient_circPartialNorm_le_of_lambdaSCap
    M L (translatePotentialSample y omega) Q u
      (t := s / 3) (r := r) (sigma := sigma) (K := B)
      (div_pos hs0 (by norm_num)) hsr hlocal.2.2.2.2.1 i N
  simpa only [Q, A, sigma] using hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
