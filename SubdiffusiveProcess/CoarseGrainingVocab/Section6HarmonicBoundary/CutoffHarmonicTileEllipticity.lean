/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.TileEllipticityCaps
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicEllipticityCaps




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **Scale-generic local error transport.**  The good-scale error at the
anchor cube `z + 𝔠_{n+2}` controls the Chapter-2 homogenization error of the
translated cube `y + 𝔠_k` for *every* scale `k` whose translate is contained
in the anchor, with the single explicit loss `3^{(s/8)(n+2−k)}`.

This is `localHomogenizationError_two_le_anchor_of_closedContainment` with the
inner scale left free; its proof is the same off-grid stability slot. -/
theorem localHomogenizationError_two_le_anchor_atScale
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L n : ℕ) (k : ℤ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
    (hcontain : translateSet (y - z) (cubeSet (originCube d k)) ⊆
      cubeSet (originCube d ((n : ℤ) + 2)))
    (hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)) :
    Ch02.HomogenizationErrorOnCube (originCube d k) (s / 6)
        .infinity (.finite 2) (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  let P : TriadicCube d := originCube d k
  let K : TriadicCube d := originCube d ((n : ℤ) + 2)
  let w : Vec d := y - z
  let A := aCutoffFamily M L (translatePotentialSample z omega)
  let A' := aCutoffFamily M L (translatePotentialSample y omega)
  let a : CoeffField d :=
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample z omega))
  let sigma : ℝ := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hrep : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = a := by
    intro Q
    rfl
  have hcompact : IsCompact (closure (cubeSet K)) :=
    (isBounded_cubeSet K).isCompact_closure
  have hnonempty : (closure (cubeSet K)).Nonempty :=
    ⟨cubeCenter K, subset_closure (cubeCenter_mem_cubeSet K)⟩
  let a0 := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L (translatePotentialSample z omega)
  have ha : Continuous a0 :=
    SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L (translatePotentialSample z omega)
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty ha.continuousOn
  have hTmeas : MeasurableSet (translateSet w (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage (measurable_id.sub measurable_const)
  have hEll : IsEllipticFieldOn (a0 xmin) (a0 xmax)
      (translateSet w (cubeSet P)) a := by
    constructor
    · have hmatrix : Continuous fun p : Vec d => scalarCoeffField a0 p :=
        ha.smul continuous_const
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      have hentry : Measurable fun p : Vec d => scalarCoeffField a0 p i j :=
        (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
      exact Measurable.ite hTmeas hentry measurable_const
    · intro p hp
      have hpK : p ∈ closure (cubeSet K) := subset_closure (hcontain hp)
      have hlow : a0 xmin ≤ a0 p := hmin hpK
      have hupp : a0 p ≤ a0 xmax := hmax hpK
      exact (isEllipticMatrix_scalarMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L (translatePotentialSample z omega) p)).mono
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L
            (translatePotentialSample z omega) xmin) hlow hupp
  have hstab := offGridErrorFunctional_le_slot
    (w := w) (P := P) (K := K) A (scalarMatrix (d := d) sigma)
      hs0 (hs.2.trans (by norm_num)) hrep hEll hcontain
  have hscale : (((K.scale - P.scale).toNat : ℕ) : ℝ) =
      ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) := rfl
  rw [hscale] at hstab
  have hframe := offGridErrorFunctional_eq_homogenizationErrorOnCube_translate
    w P (by linarith only [hs0] : 0 < s / 6) A' a
      (aCutoffFamily_coeffField_translate_sub M L omega y z)
      (scalarMatrix (d := d) sigma)
  have hparent := homogenizationErrorOnCube_aCutoff_le_section6_of_cutoffGoodEvent
    M (s := s / 8) (by linarith only [hs.1]) (by linarith only [hs.2]) L (n + 2)
      omega z hgood
  have hparent' : Ch02.HomogenizationErrorOnCube K (s / 8)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤
      section6HomogenizationError M (s / 8) L (n + 2) omega z := by
    simpa [K, A, sigma,
      Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] using hparent
  rw [← hframe]
  exact hstab.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hparent' (Real.rpow_nonneg (by norm_num) _))
    (Real.sqrt_nonneg _))

/-- The dimension-only ellipticity constant of a tile whose scale is `jj`
levels below the anchor's inner cube: `2 d (E₀² + 1)` with the error budget
`E₀ = √(192 d) · 3^{(s/8) jj} · C`. -/
def tileEllipticityConst (d : ℕ) (C s jj : ℝ) : ℝ :=
  2 * (d : ℝ) *
    ((Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * jj) * C)) ^ 2 + 1)

theorem tileEllipticityConst_pos (d : ℕ) [NeZero d] (C s jj : ℝ) :
    0 < tileEllipticityConst d C s jj := by
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  unfold tileEllipticityConst
  positivity

/-- **The good-event coarse ellipticity cap on a tile of arbitrary scale.**
For every translated cube `y + 𝔠_k` contained in the anchor `z + 𝔠_{n+2}`, the
frozen good event supplies the coarse lower-ellipticity cap

```text
(lambda_{s/3}(originCube d k ; A_y))⁻¹ ≤ tileEllipticityConst d C s (n+2−k) * σ⁻¹ ,
```

with `C` dimension-only.  This is the tile form of
`Section6HolderBelowCutoff.exists_localCutoffEllipticityCaps_nextWindow`; feeding it to
`TileCoarsePoincare.aCutoff_cubeFluctuation_lpNorm_le_of_lambdaSCap` prices the
tile's `L²` oscillation with no pointwise `aCutoff/σ` ratio anywhere. -/
theorem exists_localTileEllipticityCap (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        (Ch02.lambdaS (originCube d k) (s / 3) A)⁻¹ ≤
          tileEllipticityConst d C s ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) * sigma⁻¹ := by
  obtain ⟨C, hC, hgoodCap⟩ :=
    exists_section6HomogenizationError_le_of_cutoffGoodEvent (d := d)
  refine ⟨3 * C, by positivity, ?_⟩
  intro M s hs L n k omega y z hcontain hgood
  dsimp only
  set Q : TriadicCube d := originCube d k with hQ
  set A := aCutoffFamily M L (translatePotentialSample y omega) with hAdef
  set sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z) with hsig
  set jj : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hjj
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    rw [hsig]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    convert h using 1
  have hsection := hgoodCap M s hs L (n + 2) omega z hgood
  have hlocal := localHomogenizationError_two_le_anchor_atScale M hs L n k
    omega y z hcontain hgood
  have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
    ENNReal.toReal_nonneg
  have hE₀ : Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
      (scalarMatrix (d := d) sigma) ≤
        Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * jj) * (3 * C)) := by
    refine hlocal.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    exact hsection.trans (by linarith only [hC])
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hE₀
  simpa [tileEllipticityConst] using hcaps.2.2.2.1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
