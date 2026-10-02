/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryTileResidualCap
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicTileEllipticity




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The boundary tile price of a residual mean.**  On the frozen good event,
for every translated cube `originCube d k` whose translate lies in the anchor
`z + 𝔠_{n+2}`, and for every `H¹` function on it that vanishes on a fraction
`θ` of its volume, the square of the mean is priced by the `a`-weighted energy
with a dimension-only constant, the coarse normaliser `σ⁻¹`, the tile scale
factor squared and the single loss `3^{(s/4)(n+2−k)}`.

Nothing here uses a pointwise ellipticity ratio: the coefficient enters only
through `Ch02.lambdaS`, via `exists_localTileEllipticityCap` and the
coarse-grained `L²` Poincare inequality. -/
theorem exists_boundaryTileResidualMeanCap (d : ℕ) [NeZero d] :
    ∃ Ctile : ℝ, 0 < Ctile ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        let T := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        ∀ (w : H1Function (openCubeSet T)) (Z : Set (Vec d)) (θ : ℝ),
          MeasurableSet Z → Z ⊆ openCubeSet T → 0 < θ →
          θ * (volume (openCubeSet T)).toReal ≤ (volume Z).toReal →
          (∀ x ∈ Z, w.toFun x = 0) →
          IntegrableOn w.toFun (openCubeSet T) →
          IntegrableOn (fun x => w.toFun x ^ 2) (openCubeSet T) →
          MemLp (fun x => w.toFun x - cubeAverage T w.toFun) 2
            (volume.restrict (openCubeSet T)) →
          cubeAverage T w.toFun ^ 2 ≤
            Ctile * θ⁻¹ *
                (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                sigma⁻¹ * cubeScaleFactor T ^ 2 *
              cubeAverage T (coefficientEnergyDensity (publicCoeffField T A) w.grad) := by
  obtain ⟨C, hC, hcaps⟩ := exists_localTileEllipticityCap d
  refine ⟨2 * coarseL2PoincareConst d ^ 2 *
      (2 * (d : ℝ) * ((Real.sqrt (192 * (d : ℝ)) * C) ^ 2 + 1)) + 1, ?_, ?_⟩
  · have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have h0 : 0 ≤ coarseL2PoincareConst d := coarseL2PoincareConst_nonneg d
    positivity
  intro M s hs L n k omega y z hcontain hgood
  dsimp only
  set T : TriadicCube d := originCube d k with hT
  set A := aCutoffFamily M L (translatePotentialSample y omega) with hA
  set sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z) with hsig
  set jj : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hjj
  intro w Z θ hZmeas hZsub hθ hfrac hzero hf hf2 hmem
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    rw [hsig]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    convert h using 1
  have hcap := hcaps M s hs L n k omega y z hcontain hgood
  have hKpos : 0 < tileEllipticityConst d C s jj := tileEllipticityConst_pos d C s jj
  have hmain := sq_cubeAverage_le_of_vanishing_fraction_of_lambdaSCap
    M L (translatePotentialSample y omega) T w
    (Z := Z) (θ := θ) (t := s / 3) (sigma := sigma)
    (K := tileEllipticityConst d C s jj)
    hZmeas hZsub hθ hfrac hzero hf hf2 hmem
    (by linarith only [hs0]) (by linarith only [hs.2, hs0]) hcap
  -- expand the square of the coarse Poincare coefficient
  have hnn : (0 : ℝ) ≤ tileEllipticityConst d C s jj * sigma⁻¹ := by positivity
  have hexpand :
      (coarseL2PoincareConst d *
          Real.sqrt (tileEllipticityConst d C s jj * sigma⁻¹) * cubeScaleFactor T) ^ 2 =
        coarseL2PoincareConst d ^ 2 * (tileEllipticityConst d C s jj * sigma⁻¹) *
          cubeScaleFactor T ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnn]
  rw [hexpand] at hmain
  -- the geometric factor of the tile constant is exactly `3 ^ (s/4 * jj)`
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (s / 4 * jj) := Real.rpow_pos_of_pos (by norm_num) _
  have hsplit : tileEllipticityConst d C s jj ≤
      (3 : ℝ) ^ (s / 4 * jj) *
        (2 * (d : ℝ) * ((Real.sqrt (192 * (d : ℝ)) * C) ^ 2 + 1)) := by
    have hsq : ((3 : ℝ) ^ (s / 8 * jj)) ^ 2 = (3 : ℝ) ^ (s / 4 * jj) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (s / 8 * jj)) 2, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (s / 4 * jj) := by
      refine Real.one_le_rpow (by norm_num) ?_
      have hjjnn : 0 ≤ jj := by
        rw [hjj]; positivity
      positivity
    unfold tileEllipticityConst
    have hrew :
        (Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * jj) * C)) ^ 2 =
          (3 : ℝ) ^ (s / 4 * jj) * (Real.sqrt (192 * (d : ℝ)) * C) ^ 2 := by
      rw [mul_pow, mul_pow, ← hsq]
      ring
    rw [hrew]
    have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    nlinarith [hone, sq_nonneg (Real.sqrt (192 * (d : ℝ)) * C), hd0]
  set B0 : ℝ := 2 * (d : ℝ) * ((Real.sqrt (192 * (d : ℝ)) * C) ^ 2 + 1) with hB0
  set Ctile : ℝ := 2 * coarseL2PoincareConst d ^ 2 * B0 + 1 with hCtile
  set E : ℝ := cubeAverage T (coefficientEnergyDensity (publicCoeffField T A) w.grad) with hE
  have hEll := publicCoeffField_isEllipticFieldOn_cubeSet T A
  have hEnonneg : 0 ≤ E := by
    rw [hE]
    refine cubeAverage_nonneg_of_nonneg_on ?_
    intro x hx
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll w.grad x hx
  have hscale2 : (0 : ℝ) ≤ cubeScaleFactor T ^ 2 := sq_nonneg _
  have hcoeff : (0 : ℝ) ≤ 2 * θ⁻¹ * coarseL2PoincareConst d ^ 2 * sigma⁻¹ := by
    have := coarseL2PoincareConst_nonneg d
    positivity
  refine hmain.trans ?_
  have hstep :
      2 * θ⁻¹ *
          (coarseL2PoincareConst d ^ 2 * (tileEllipticityConst d C s jj * sigma⁻¹) *
            cubeScaleFactor T ^ 2) * E ≤
        2 * θ⁻¹ *
          (coarseL2PoincareConst d ^ 2 *
            (((3 : ℝ) ^ (s / 4 * jj) * B0) * sigma⁻¹) *
            cubeScaleFactor T ^ 2) * E := by
    have hmul : tileEllipticityConst d C s jj * sigma⁻¹ ≤
        ((3 : ℝ) ^ (s / 4 * jj) * B0) * sigma⁻¹ :=
      mul_le_mul_of_nonneg_right hsplit (by positivity)
    have hθnn : (0 : ℝ) ≤ 2 * θ⁻¹ := by positivity
    have hPnn : (0 : ℝ) ≤ coarseL2PoincareConst d ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right hmul hscale2
    nlinarith [this, hθnn, hPnn, hEnonneg, hscale2]
  refine hstep.trans ?_
  have hBig : 2 * coarseL2PoincareConst d ^ 2 * B0 ≤ Ctile := by
    rw [hCtile]; linarith
  have hfactors : (0 : ℝ) ≤ θ⁻¹ * ((3 : ℝ) ^ (s / 4 * jj) * (sigma⁻¹ *
      (cubeScaleFactor T ^ 2 * E))) := by
    have : (0 : ℝ) ≤ sigma⁻¹ := by positivity
    positivity
  nlinarith [hBig, hfactors]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
