import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalTransport
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.WindowGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorScaleGeometry
import Homogenization.Sobolev.Fractional.ExactOverlapEuclideanLpComparison




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The force overlap slot.**  The positive Besov overlap seminorm of the
recentred force on the replacement cube is bounded by the frozen fractional
seminorm of the force on the manuscript window, with a dimension-only constant
and the single explicit factor `s^{-1/2}`. -/
theorem exists_interiorForceOverlap_le_windowSeminorm (d : ℕ) [NeZero d] :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (sOrder : FractionalOrder) (m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ∀ (g g0 : Vec d → Vec d),
        Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d ((n : ℤ) - 2)) sOrder FiniteLpExponent.two g0 →
        (∀ p, g0 p = g (p + y)) →
        Ch03.ABK26.cubeEuclideanPositiveBesovOverlapESeminorm
            (originCube d ((n : ℤ) - 2)) sOrder FiniteLpExponent.two g0 ≤
          ENNReal.ofReal (Cd * Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
            (fractionalSeminormOn (truncatedCube d (m : ℤ) (n : ℤ) x)
              sOrder.1 g).toReal) := by
  refine ⟨max 1 ((cubeEuclideanWspOverlapDimensionConstant d).toReal *
    (3 : ℝ) ^ d), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro sOrder m n hnm z x y hx hD g g0 hg hg0 hg0eq
  set Q : TriadicCube d := originCube d ((n : ℤ) - 2) with hQ
  set U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x with hU
  set P : Set (Vec d) := translateSet y (openCubeSet Q) with hP
  have hPset : P = translatedCube d ((n : ℤ) - 2) y := by
    rw [hP, hQ, translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  -- geometry of the two windows
  have hPU : P ⊆ U := by
    rw [hPset, hU]
    exact hD.trans (Section6ExcessDecay.truncatedCube_mono d (m : ℤ) x
      (by omega))
  have hPpos : 0 < (volume P).toReal := by
    rw [hP, volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hUpos : 0 < (volume U).toReal := by
    rw [hU]
    exact Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain
      (by omega)
  have hPtop : volume P ≠ ⊤ := by
    rw [hP, volume_translateSet_eq]
    exact (volume_openCubeSet_lt_top Q).ne
  have hUtop : volume U ≠ ⊤ := by
    rw [hU]
    exact (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ)
      (n : ℤ) x).ne
  have hP0 : volume P ≠ 0 := by
    intro hzero
    rw [hzero] at hPpos
    simp at hPpos
  have hU0 : volume U ≠ 0 := by
    intro hzero
    rw [hzero] at hUpos
    simp at hUpos
  -- finiteness of the window seminorm
  have hgUfin : fractionalSeminormOn U sOrder.1 g ≠ ⊤ := by
    have hfrac : MemFractionalOn (cube d (m : ℤ)) sOrder.1 g := by
      change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ)))
        sOrder.1 g ≠ ⊤
      rw [fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm]
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hg.2.eSeminorm_lt_top.ne
    rw [hU]
    exact memFractionalOn_truncatedCube_of_domain hxDomain (by omega) hfrac
  -- the dimension-only overlap comparison
  let F : CubeEuclideanLpField Q FiniteLpExponent.two := ⟨g0, hg0.1⟩
  have hcmp := cubeEuclideanOverlap_le_dimensionConstant_mul_wsp Q sOrder
    FiniteLpExponent.two F
  have hwfin : cubeEuclideanWspESeminorm Q sOrder FiniteLpExponent.two g0 ≠ ⊤ :=
    hg0.2.eSeminorm_lt_top.ne
  have hctop : cubeEuclideanWspOverlapDimensionConstant d ≠ ⊤ :=
    (cubeEuclideanWspOverlapDimensionConstant_lt_top d).ne
  have hcmp' : Ch03.ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q sOrder
      FiniteLpExponent.two g0 ≤
      ENNReal.ofReal ((cubeEuclideanWspOverlapDimensionConstant d).toReal *
        (cubeEuclideanWspESeminorm Q sOrder FiniteLpExponent.two g0).toReal) := by
    rw [← ENNReal.toReal_mul,
      ENNReal.ofReal_toReal (ENNReal.mul_ne_top hctop hwfin)]
    exact hcmp
  refine hcmp'.trans (ENNReal.ofReal_le_ofReal ?_)
  -- unfold the Wsp seminorm into the frozen fractional seminorm
  rw [cubeEuclideanWspESeminorm_toReal_eq_rpow_neg_half_mul_fractional]
  -- recentre, then enlarge to the manuscript window
  have hg0fun : g0 = fun p ↦ g (p + y) := funext hg0eq
  have htrans : fractionalSeminormOn (openCubeSet Q) sOrder.1 g0 =
      fractionalSeminormOn P sOrder.1 g := by
    rw [hP, fractionalSeminormOn_translateSet, hg0fun]
  have hmono : (fractionalSeminormOn P sOrder.1 g).toReal ≤
      Real.sqrt ((volume U).toReal / (volume P).toReal) *
        (fractionalSeminormOn U sOrder.1 g).toReal :=
    fractionalSeminormOn_toReal_mono_set hPU hP0 hPtop hU0 hUtop
      sOrder.1 g hgUfin
  have hratio : (volume U).toReal / (volume P).toReal ≤ (9 : ℝ) ^ d := by
    rw [hU, hPset]
    exact volume_ratio_truncatedCube_translated_predTwo_le hxDomain (by omega)
  have hsqrt : Real.sqrt ((volume U).toReal / (volume P).toReal) ≤
      (3 : ℝ) ^ d := by
    have h9 : ((3 : ℝ) ^ d) ^ 2 = (9 : ℝ) ^ d := by
      rw [← pow_mul, show d * 2 = 2 * d by ring, pow_mul]
      norm_num
    have := Real.sqrt_le_sqrt hratio
    rwa [← h9, Real.sqrt_sq (by positivity)] at this
  have hG0 : 0 ≤ (fractionalSeminormOn U sOrder.1 g).toReal :=
    ENNReal.toReal_nonneg
  have hrpow0 : 0 ≤ Real.rpow sOrder.1 (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg sOrder.2.1.le _
  have hC0 : 0 ≤ (cubeEuclideanWspOverlapDimensionConstant d).toReal :=
    ENNReal.toReal_nonneg
  have hstep : (fractionalSeminormOn (openCubeSet Q) sOrder.1 g0).toReal ≤
      (3 : ℝ) ^ d * (fractionalSeminormOn U sOrder.1 g).toReal := by
    rw [htrans]
    exact hmono.trans (mul_le_mul_of_nonneg_right hsqrt hG0)
  calc
    (cubeEuclideanWspOverlapDimensionConstant d).toReal *
        (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (fractionalSeminormOn (openCubeSet Q) sOrder.1 g0).toReal) ≤
        (cubeEuclideanWspOverlapDimensionConstant d).toReal *
          (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
            ((3 : ℝ) ^ d * (fractionalSeminormOn U sOrder.1 g).toReal)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hstep hrpow0) hC0
    _ = ((cubeEuclideanWspOverlapDimensionConstant d).toReal * (3 : ℝ) ^ d) *
          Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (fractionalSeminormOn U sOrder.1 g).toReal := by ring
    _ ≤ max 1 ((cubeEuclideanWspOverlapDimensionConstant d).toReal *
          (3 : ℝ) ^ d) * Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (fractionalSeminormOn U sOrder.1 g).toReal := by
      apply mul_le_mul_of_nonneg_right _ hG0
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hrpow0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
