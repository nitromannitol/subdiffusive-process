
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffEllipticityCaps

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

noncomputable section

variable {d : ℕ}

/-- Cutoff companion of
`Section6HarmonicApproximation.localHomogenizationError_two_le_anchor`: the
closed-containment window form, with `n + 2 ≤ L` deleted. -/
theorem localHomogenizationError_two_le_anchor
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x y z : Vec d)
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hD : translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x)
    (hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  apply localHomogenizationError_two_le_cutoffAnchor_of_closedContainment M hs L n
    omega y z
  · exact closedOffGridCube_subset_originAnchorParent
      (m := (m : ℤ)) (n := (n : ℤ)) hx hD
  · exact hgood

/-- **The finite-cutoff boundary ellipticity caps, closed-containment form.**
Companion of `Section6HarmonicApproximation.exists_localBoundaryEllipticityCaps`
on `𝒢^{(L)}_{n+2,z}`, with the binder `n + 2 ≤ L` deleted. -/
theorem exists_localBoundaryEllipticityCaps (d : ℕ) [NeZero d] :
    ∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
              (scalarMatrix (d := d) sigma) ≤ E₀ ∧
          sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
          sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
          Ch02.LambdaS Q (1 / 2) A ≤ B * sigma ∧
          (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ ∧
          Ch02.lambdaS Q (s / 3) A ≤ B * sigma ∧
          Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ) := by
  obtain ⟨C, hC, hgoodCap⟩ :=
    exists_section6HomogenizationError_le_of_cutoffGoodEvent (d := d)
  let E₀ : ℝ := Real.sqrt (192 * (d : ℝ)) * (3 * C)
  let B : ℝ := 2 * (d : ℝ) * (E₀ ^ 2 + 1)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hE₀ : 0 < E₀ := by
    dsimp [E₀]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨E₀, B, hE₀, hB, ?_⟩
  intro M s hs L m n z x y omega hx hD hgood
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! h
  have hsection := hgoodCap M s hs L (n + 2) omega z hgood
  have hlocal := localHomogenizationError_two_le_anchor M hs
    (L := L) (m := m) (n := n) omega x y z hx hD hgood
  have hexp : s / 8 * (4 : ℝ) ≤ 1 := by linarith only [hs.2]
  have hpow : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 3 := by norm_num
  have hlocalCap : Ch02.HomogenizationErrorOnCube Q (s / 6)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E₀ := by
    refine hlocal.trans ?_
    have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
      ENNReal.toReal_nonneg
    have hinner : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
        section6HomogenizationError M (s / 8) L (n + 2) omega z ≤ 3 * C :=
      (mul_le_mul_of_nonneg_right hpow hsec0).trans
        (mul_le_mul_of_nonneg_left hsection (by norm_num))
    exact mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg _)
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hlocalCap
  simpa only [Q, A, sigma, B] using ⟨hlocalCap, hcaps⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
