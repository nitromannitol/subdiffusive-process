module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffErrorCap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffLocalError

@[expose] public section

/-!
# Good-event ellipticity caps at a finite cutoff

`Section6HarmonicApproximation.exists_localBoundaryEllipticityCaps` and its
`_nextWindow` companion are the single point at which the whole interior
harmonic-approximation chain consumes the good event: everything downstream
(the projected cell readout, the depth-two cover, the weighted-energy slot and
the sharp comparator loop) uses only the seven scalar caps produced here.

The two ingredients of those theorems are

* the good-event error cap `section6HomogenizationError ≤ C`, and
* the transport of that error to the off-grid comparison cube.

Both now exist in cutoff form with **no relation between `L` and the scale**
(`CutoffErrorCap.lean`, `CutoffLocalError.lean`), and the conversion of an
error cap into ellipticity caps,
`Section6HarmonicApproximation.localBoundaryEllipticityCaps_of_errorCap`, is
entirely deterministic.  This module therefore assembles the cutoff caps by
quoting that deterministic converter.

paper label `e.bound.Lambdas.by.Es`; "the normalized ellipticity
bounds used there follow from `e.cutoff.regularity.good.E.epsilon` and
`e.bound.Lambdas.by.Es`".
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The `E₀`/`B` pair of the cutoff caps, and the error cap in the shape the
deterministic converter consumes. -/
private theorem cutoffErrorCapPair (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ,
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        x ∈ truncatedCube d m (n - 3) z →
        y ∈ truncatedCube d m n x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
            .infinity (.finite 2)
            (aCutoffFamily M L (translatePotentialSample y omega))
            (scalarMatrix (d := d)
              (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
          Real.sqrt (192 * (d : ℝ)) * (3 * C) := by
  obtain ⟨C, hC, hcap⟩ :=
    exists_section6HomogenizationError_le_of_cutoffGoodEvent (d := d)
  refine ⟨C, hC, ?_⟩
  intro M s hs L m n z x y omega hx hy hgood
  refine (localHomogenizationError_two_le_cutoffAnchor_nextWindow
    M hs L m n omega x y z hx hy hgood).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hexp : s / 8 * (4 : ℝ) ≤ 1 := by linarith only [hs.2]
  have hpow : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 3 := by norm_num
  have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
    ENNReal.toReal_nonneg
  exact (mul_le_mul_of_nonneg_right hpow hsec0).trans
    (mul_le_mul_of_nonneg_left (hcap M s hs L (n + 2) omega z hgood) (by norm_num))

/-- **The finite-cutoff ellipticity caps.**  Companion of
`Section6HarmonicApproximation.exists_localBoundaryEllipticityCaps_nextWindow`
on the good event `𝒢^{(L)}_{n+2,z}`, with the binder `n + 2 ≤ L` deleted. -/
theorem exists_localCutoffEllipticityCaps_nextWindow (d : ℕ) [NeZero d] :
    ∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        y ∈ truncatedCube d m n x →
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
  obtain ⟨C, hC, hcap⟩ := cutoffErrorCapPair d
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
  intro M s hs L m n z x y omega hx hy hgood
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
  have hlocalCap : Ch02.HomogenizationErrorOnCube Q (s / 6)
      .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E₀ :=
    hcap M s hs L m n z x y omega hx hy hgood
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hlocalCap
  simpa only [Q, A, sigma, B] using ⟨hlocalCap, hcaps⟩

/-- The comparison-cube variant, for a replacement cube `y + cube_(n-2)`
sitting inside the next truncated window. -/
theorem exists_localCutoffEllipticityCaps (d : ℕ) [NeZero d] :
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
  obtain ⟨C, hC, hcapNext⟩ :=
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
  have hcontain : translateSet (y - z)
      (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        cubeSet (originCube d ((n : ℤ) + 2)) :=
    closedOffGridCube_subset_originAnchorParent (m := (m : ℤ)) (n := (n : ℤ)) hx hD
  have hlocal := localHomogenizationError_two_le_cutoffAnchor_of_closedContainment
    M hs L n omega y z hcontain hgood
  have hexp : s / 8 * (4 : ℝ) ≤ 1 := by linarith only [hs.2]
  have hpow : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 3 := by norm_num
  have hlocalCap : Ch02.HomogenizationErrorOnCube Q (s / 6)
      .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E₀ := by
    refine hlocal.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
      ENNReal.toReal_nonneg
    exact (mul_le_mul_of_nonneg_right hpow hsec0).trans
      (mul_le_mul_of_nonneg_left (hcapNext M s hs L (n + 2) omega z hgood)
        (by norm_num))
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hlocalCap
  simpa only [Q, A, sigma, B] using ⟨hlocalCap, hcaps⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
