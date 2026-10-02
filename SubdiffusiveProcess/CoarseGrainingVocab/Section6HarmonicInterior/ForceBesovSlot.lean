import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.ForceOverlapSlot
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.DatumPricing




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The direct forcing slot.**  The note-normalized positive Besov seminorm
of the recentred force at any order `t ≤ s` on the replacement cube is bounded
by the frozen window seminorm at order `s`, with a dimension-only constant,
the manuscript scale factor `3^{sn}` and the single explicit `s^{-1/2}`. -/
theorem exists_interiorForceBesov_le_windowSeminorm (d : ℕ) [NeZero d] :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (sOrder : FractionalOrder) (m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ∀ g : Vec d → Vec d,
        Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
      ∀ t : ℝ, t ≤ sOrder.1 →
        scaleNormalizedPositiveBesovVectorSeminormTwo
            (originCube d ((n : ℤ) - 2)) t (fun p ↦ g (p + y)) ≤
          Cb * (3 : ℝ) ^ (sOrder.1 * (n : ℝ)) *
            sOrder.1 ^ (-(1 / 2 : ℝ)) *
            (fractionalSeminormOn (truncatedCube d (m : ℤ) (n : ℤ) x)
              sOrder.1 g).toReal := by
  refine ⟨caccioppoliExactDatumConstant d * (3 : ℝ) ^ d,
    mul_pos (caccioppoliExactDatumConstant_pos d) (by positivity), ?_⟩
  intro sOrder m n hnm z x y hx hD g hg t hts
  set Q : TriadicCube d := originCube d ((n : ℤ) - 2) with hQ
  set U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x with hU
  set P : Set (Vec d) := translateSet y (openCubeSet Q) with hP
  have hPset : P = translatedCube d ((n : ℤ) - 2) y := by
    rw [hP, hQ, translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  have hPopen : P ⊆ openCubeSet (originCube d (m : ℤ)) := by
    rw [hPset]
    intro p hp
    exact (hD hp).2
  -- the recentred force is a full Euclidean datum on the replacement cube
  have hglocal : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q sOrder FiniteLpExponent.two (fun p ↦ g (p + y)) :=
    memCubeEuclideanFullWsp_translate_of_subset Q (originCube d (m : ℤ)) y
      sOrder FiniteLpExponent.two g hPopen hg
  -- geometry
  have hPU : P ⊆ U := by
    rw [hPset, hU]
    exact hD.trans (Section6ExcessDecay.truncatedCube_mono d (m : ℤ) x (by omega))
  have hPpos : 0 < (volume P).toReal := by
    rw [hP, volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hUpos : 0 < (volume U).toReal := by
    rw [hU]
    exact Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain (by omega)
  have hPtop : volume P ≠ ⊤ := by
    rw [hP, volume_translateSet_eq]
    exact (volume_openCubeSet_lt_top Q).ne
  have hUtop : volume U ≠ ⊤ := by
    rw [hU]
    exact (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ) (n : ℤ) x).ne
  have hP0 : volume P ≠ 0 := by
    intro hzero
    rw [hzero] at hPpos
    simp at hPpos
  have hU0 : volume U ≠ 0 := by
    intro hzero
    rw [hzero] at hUpos
    simp at hUpos
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
  -- order monotonicity of the positive Besov seminorm
  have hreg : Ch03.Legacy.ForceSobolevRegularity Q sOrder.1
      (fun p ↦ g (p + y)) :=
    cubeEuclideanWspField_forceSobolevRegularity sOrder
      { toField := fun p ↦ g (p + y)
        euclideanMemLp := hglocal.1
        euclideanMemWsp := hglocal.2 }
  have hbesovReg : Ch03.ForceBesovRegularity Q sOrder.1 (fun p ↦ g (p + y)) :=
    hreg.toForceBesovRegularity sOrder.2.1 sOrder.2.2.le
  have hdrop : scaleNormalizedPositiveBesovVectorSeminormTwo Q t
        (fun p ↦ g (p + y)) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
        (fun p ↦ g (p + y)) :=
    cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove Q
      (fun p ↦ g (p + y)) hts hbesovReg.partialSeminorms_bddAbove
  -- the exact-datum window price
  have hwindow := scaleNormalizedPositiveBesovVectorSeminormTwo_translate_le_window
    Q y U sOrder g hglocal hPU hP0 hPtop hU0 hUtop hgUfin
  refine hdrop.trans (hwindow.trans ?_)
  -- collect the geometric factors
  have hratio : (volume U).toReal / (volume P).toReal ≤ (9 : ℝ) ^ d := by
    rw [hU, hPset]
    exact volume_ratio_truncatedCube_translated_predTwo_le hxDomain (by omega)
  have hsqrt : Real.sqrt ((volume U).toReal / (volume P).toReal) ≤ (3 : ℝ) ^ d := by
    have h9 : ((3 : ℝ) ^ d) ^ 2 = (9 : ℝ) ^ d := by
      rw [← pow_mul, show d * 2 = 2 * d by ring, pow_mul]
      norm_num
    have hs := Real.sqrt_le_sqrt hratio
    rwa [← h9, Real.sqrt_sq (by positivity)] at hs
  have hweight : cubeBesovScaleWeight (-sOrder.1) Q ≤
      (3 : ℝ) ^ (sOrder.1 * (n : ℝ)) := by
    rw [hQ, cubeBesovScaleWeight_neg_origin_predTwo]
    exact rpow_projected_fractional_le sOrder.2.1 n
  have hG0 : 0 ≤ (fractionalSeminormOn U sOrder.1 g).toReal := ENNReal.toReal_nonneg
  have hrp0 : 0 ≤ sOrder.1 ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg sOrder.2.1.le _
  have hC0 : 0 ≤ caccioppoliExactDatumConstant d :=
    (caccioppoliExactDatumConstant_pos d).le
  have hweight0 : 0 ≤ cubeBesovScaleWeight (-sOrder.1) Q :=
    cubeBesovScaleWeight_nonneg _ _
  calc
    caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
        (sOrder.1 ^ (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal / (volume P).toReal) *
            (fractionalSeminormOn U sOrder.1 g).toReal)) ≤
        caccioppoliExactDatumConstant d * (3 : ℝ) ^ (sOrder.1 * (n : ℝ)) *
          (sOrder.1 ^ (-(1 / 2 : ℝ)) *
            ((3 : ℝ) ^ d * (fractionalSeminormOn U sOrder.1 g).toReal)) := by
      gcongr
    _ = caccioppoliExactDatumConstant d * (3 : ℝ) ^ d *
          (3 : ℝ) ^ (sOrder.1 * (n : ℝ)) * sOrder.1 ^ (-(1 / 2 : ℝ)) *
          (fractionalSeminormOn U sOrder.1 g).toReal := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
