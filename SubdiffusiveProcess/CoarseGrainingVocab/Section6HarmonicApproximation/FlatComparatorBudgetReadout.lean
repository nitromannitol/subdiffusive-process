import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorErrorLoop




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Uniform order bounds for the spectral readout -/

/-- On the manuscript order corridor, the elementary linear-competitor
interpolation integral is bounded by the length of the unit interval. -/
theorem linearKSeminormIntegral_le_one
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4) :
    Section6Dirichlet.linearKSeminormIntegral s ≤ 1 := by
  unfold Section6Dirichlet.linearKSeminormIntegral
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.rpow t (1 - 2 * s.1))) ≤
        ∫⁻ _t in Set.Ioo (0 : ℝ) 1, (1 : ℝ≥0∞) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [ENNReal.ofReal_le_one]
      exact Real.rpow_le_one ht.1.le ht.2.le (by linarith)
    _ = 1 := by simp

theorem linearKSeminormConstant_le_one
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4) :
    Section6Dirichlet.linearKSeminormConstant s ≤ 1 := by
  unfold Section6Dirichlet.linearKSeminormConstant
  simpa using ENNReal.rpow_le_rpow (linearKSeminormIntegral_le_one s hs)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- A fixed positive lower bound for the triadic lower-series factor on the
orders used by the manuscript. -/
theorem triadicContinuousKLowerSeriesConstant_lower
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4) :
    ENNReal.ofReal (2 / 9 : ℝ) ≤ triadicContinuousKLowerSeriesConstant s := by
  have hpow : (1 / 3 : ℝ) ≤ Real.rpow 3 (-2 * s.1) := by
    calc
      (1 / 3 : ℝ) = Real.rpow 3 (-1 : ℝ) := by
        change (1 / 3 : ℝ) = (3 : ℝ) ^ (-1 : ℝ)
        rw [Real.rpow_neg_one]
        norm_num
      _ ≤ Real.rpow 3 (-2 * s.1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  unfold triadicContinuousKLowerSeriesConstant
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

theorem triadicContinuousKLowerSeriesConstant_inv_rpow_half_le_nine
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4) :
    (triadicContinuousKLowerSeriesConstant s)⁻¹ ^ (1 / 2 : ℝ) ≤ 9 := by
  have hinv : (triadicContinuousKLowerSeriesConstant s)⁻¹ ≤ 9 := by
    calc
      (triadicContinuousKLowerSeriesConstant s)⁻¹ ≤
          (ENNReal.ofReal (2 / 9 : ℝ))⁻¹ :=
        ENNReal.inv_le_inv' (triadicContinuousKLowerSeriesConstant_lower s hs)
      _ ≤ (ENNReal.ofReal (1 / 9 : ℝ))⁻¹ := by
        exact ENNReal.inv_le_inv' (ENNReal.ofReal_le_ofReal (by norm_num))
      _ ≤ 9 := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 9)]
        norm_num
  calc
    (triadicContinuousKLowerSeriesConstant s)⁻¹ ^ (1 / 2 : ℝ) ≤
        (9 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hinv (by norm_num)
    _ ≤ (9 : ℝ≥0∞) ^ (1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 9 := by simp

omit [NeZero d] in
theorem euclideanHsToContinuousKSeminormConstant_le
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4) :
    euclideanHsToContinuousKSeminormConstant s d ≤
      (allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 := by
  unfold euclideanHsToContinuousKSeminormConstant
  exact mul_le_mul_right (by
    rw [max_le_iff]
    exact ⟨by norm_num,
      triadicContinuousKLowerSeriesConstant_inv_rpow_half_le_nine s hs⟩) _

omit [NeZero d] in
theorem scaledVectorDatumFractionalConstant_le
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4) :
    Section6Dirichlet.scaledVectorDatumFractionalConstant s d ≤
      (allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 := by
  have hsOne : ENNReal.ofReal s.1 ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    linarith
  have hsHalf : (ENNReal.ofReal s.1) ^ (1 / 2 : ℝ) ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow hsOne (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hlinear : max 1 (Section6Dirichlet.linearKSeminormConstant s) = 1 :=
    max_eq_left (linearKSeminormConstant_le_one s hs)
  unfold Section6Dirichlet.scaledVectorDatumFractionalConstant
  rw [hlinear, mul_one]
  calc
    (ENNReal.ofReal s.1) ^ (1 / 2 : ℝ) *
        euclideanHsToContinuousKSeminormConstant s d ≤
      1 * ((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9) :=
        mul_le_mul hsHalf (euclideanHsToContinuousKSeminormConstant_le s hs)
          (by positivity) (by positivity)
    _ = _ := one_mul _

/-- Dimension-only coefficient left after extracting the single explicit
`s⁻¹/²` factor from the spectral readout. -/
noncomputable def flatComparatorSpectralOrderConstant
    (d : ℕ) [NeZero d] : ℝ≥0∞ :=
  2 * ((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1) *
    ENNReal.ofReal (Section6Dirichlet.unitDivergenceLiftConstant d)

theorem flatComparatorSpectralOrderConstant_lt_top
    (d : ℕ) [NeZero d] : flatComparatorSpectralOrderConstant d < ∞ := by
  unfold flatComparatorSpectralOrderConstant
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top
    · norm_num
    · apply ENNReal.add_lt_top.2
      exact ⟨ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (allDimensionalHsToSampleConstant_lt_top d).ne) (by norm_num),
        ENNReal.one_lt_top⟩
  · exact ENNReal.ofReal_lt_top

theorem dirichletSpectralReadoutConstant_le_orderFactor
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4) :
    Section6Dirichlet.dirichletSpectralReadoutConstant s d ≤
      (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
        flatComparatorSpectralOrderConstant d := by
  have hscaled := scaledVectorDatumFractionalConstant_le (d := d) s hs
  have hexp : -(FiniteLpExponent.two.exponent.toReal)⁻¹ = -(1 / 2 : ℝ) := by
    norm_num [FiniteLpExponent.two_exponent]
  unfold Section6Dirichlet.dirichletSpectralReadoutConstant
    Section6Dirichlet.spectralPositiveReadoutConstant
    flatComparatorSpectralOrderConstant
  rw [hexp]
  calc
    2 * ((ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
          (Section6Dirichlet.scaledVectorDatumFractionalConstant s d + 1)) *
        ENNReal.ofReal (Section6Dirichlet.unitDivergenceLiftConstant d) ≤
      2 * ((ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
          ((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1)) *
        ENNReal.ofReal (Section6Dirichlet.unitDivergenceLiftConstant d) := by
      gcongr
    _ = (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
        (2 * ((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1) *
          ENNReal.ofReal (Section6Dirichlet.unitDivergenceLiftConstant d)) := by ring

theorem dirichletSpectralReadoutConstant_toReal_le
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4) :
    (Section6Dirichlet.dirichletSpectralReadoutConstant s d).toReal ≤
      (flatComparatorSpectralOrderConstant d).toReal *
        Real.rpow s.1 (-(1 / 2 : ℝ)) := by
  have htop : (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
      flatComparatorSpectralOrderConstant d ≠ ∞ := by
    exact (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.ofReal_ne_zero_iff.mpr s.2.1) ENNReal.ofReal_ne_top))
      (flatComparatorSpectralOrderConstant_lt_top d)).ne
  have h := ENNReal.toReal_mono htop
    (dirichletSpectralReadoutConstant_le_orderFactor (d := d) s hs)
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal s.2.1.le, mul_comm] using h

/-- A real upper bound for the exact extended-real local coarse-graining
budget.  All four payload slots are assumed nonnegative, as they are in the
PDE application. -/
theorem flatComparatorLocalCoarseBound_toReal_le
    (C : ℝ≥0∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (E1 E2 S D : ℝ) (n : ℤ)
    (hss2 : s.1 < s2.1)
    (hsigma : 0 < sigma) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hS : 0 ≤ S) (hD : 0 ≤ D) :
    (flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D n).toReal ≤
      Real.rpow s.1 (-(1 / 2 : ℝ)) *
        (C.toReal * s.1⁻¹ * Real.sqrt sigma * Real.rpow 3 s1.1 * E1 * S +
          C.toReal * Real.rpow s.1 (-(9 / 2 : ℝ)) *
            (s2.1 - s.1)⁻¹ *
            (1 + (Real.rpow 3 (s1.1 / 2) * E2) ^ 2) *
            Real.rpow 3 (s2.1 * (n : ℝ)) * D) := by
  let A : ℝ≥0∞ :=
    C * (ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma) ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal (Real.rpow 3 s1.1) * ENNReal.ofReal E1) *
      ENNReal.ofReal S
  let B : ℝ≥0∞ :=
    C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
      (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
      (1 + (ENNReal.ofReal (Real.rpow 3 (s1.1 / 2)) *
        ENNReal.ofReal E2) ^ 2) *
      ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) * ENNReal.ofReal D
  have hs0 : 0 ≤ s.1 := s.2.1.le
  have hgap0 : 0 ≤ s2.1 - s.1 := sub_nonneg.mpr hss2.le
  have hthree1 : 0 ≤ Real.rpow (3 : ℝ) s1.1 :=
    Real.rpow_nonneg (by norm_num) _
  have hthreeHalf : 0 ≤ Real.rpow (3 : ℝ) (s1.1 / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hthreeN : 0 ≤ Real.rpow (3 : ℝ) (s2.1 * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hAeq : A.toReal =
      C.toReal * s.1⁻¹ * Real.sqrt sigma * Real.rpow 3 s1.1 * E1 * S := by
    dsimp only [A]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hs0,
      ENNReal.toReal_ofReal hsigma.le, ENNReal.toReal_ofReal hE1,
      ENNReal.toReal_ofReal hS, ENNReal.toReal_ofReal hthree1]
    rw [Real.sqrt_eq_rpow]
    ring
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s1.1 / 2)) *
    ENNReal.ofReal E2
  have hTtop : T ≠ ∞ := by
    dsimp only [T]
    finiteness
  have hTreal : T.toReal = Real.rpow 3 (s1.1 / 2) * E2 := by
    dsimp only [T]
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hthreeHalf,
      ENNReal.toReal_ofReal hE2]
  have hTpowtop : T ^ 2 ≠ ∞ := by finiteness
  have hinner : (1 + T ^ 2).toReal =
      1 + (Real.rpow 3 (s1.1 / 2) * E2) ^ 2 := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top hTpowtop,
      ENNReal.toReal_one, ENNReal.toReal_pow, hTreal]
  have hBeq : B.toReal =
      C.toReal * Real.rpow s.1 (-(9 / 2 : ℝ)) *
        (s2.1 - s.1)⁻¹ *
        (1 + (Real.rpow 3 (s1.1 / 2) * E2) ^ 2) *
        Real.rpow 3 (s2.1 * (n : ℝ)) * D := by
    change (C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
      (ENNReal.ofReal (s2.1 - s.1))⁻¹ * (1 + T ^ 2) *
      ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
      ENNReal.ofReal D).toReal = _
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hs0,
      ENNReal.toReal_ofReal hgap0, hinner,
      ENNReal.toReal_ofReal hD, ENNReal.toReal_ofReal hthreeN]
    rw [show s.1 ^ (-(9 / 2 : ℝ)) =
      Real.rpow s.1 (-(9 / 2 : ℝ)) by rfl]
  have hadd : (A + B).toReal ≤ A.toReal + B.toReal := ENNReal.toReal_add_le
  unfold flatComparatorLocalCoarseBound
  change ((ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) * (A + B)).toReal ≤ _
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hs0]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hs0 _)
  rw [hAeq, hBeq] at hadd
  exact hadd

/-- Real-valued form of the complete flat-comparator loop, including the
spectral readout and the direct scalar-forcing term. -/
theorem flatComparatorGoodEventLoopBound_le_realReadout
    (C : ℝ≥0∞) (d n : ℕ) [NeZero d] (sigma : ℝ)
    (smid s1 s2 : FractionalOrder) (E S D : ℝ)
    (Q : TriadicCube d) (g : Vec d → Vec d)
    (hmid2 : smid.1 < s2.1) (hsigma : 0 < sigma)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    flatComparatorGoodEventLoopBound C d n sigma smid s1 s2 E S D Q g ≤
      (Section6Dirichlet.dirichletSpectralReadoutConstant smid d).toReal *
        centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
          (Real.rpow smid.1 (-(1 / 2 : ℝ)) *
            (C.toReal * smid.1⁻¹ * Real.sqrt sigma *
                Real.rpow 3 s1.1 * E * S +
              C.toReal * Real.rpow smid.1 (-(9 / 2 : ℝ)) *
                (s2.1 - smid.1)⁻¹ *
                (1 + (Real.rpow 3 (s1.1 / 2) * E) ^ 2) *
                Real.rpow 3 (s2.1 * (((n : ℤ) - 3 : ℤ) : ℝ)) * D)) +
        unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
          (d : ℝ) * sigma⁻¹ *
            (Real.sqrt (Fintype.card (Fin d) : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  have hbudget := flatComparatorLocalCoarseBound_toReal_le
    C sigma smid s1 s2 E E S D ((n : ℤ) - 3)
      hmid2 hsigma hE hE hS hD
  have hscale : 0 ≤ centeredCubeScale ((n : ℤ) - 2) :=
    (centeredCubeScale_pos ((n : ℤ) - 2)).le
  have hinv : 0 ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  have hbudget0 : 0 ≤
      (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
        ((n : ℤ) - 3)).toReal := ENNReal.toReal_nonneg
  have hreal0 : 0 ≤ centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
      (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
        ((n : ℤ) - 3)).toReal := by positivity
  unfold flatComparatorGoodEventLoopBound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hreal0]
  let R : ℝ := Real.rpow smid.1 (-(1 / 2 : ℝ)) *
    (C.toReal * smid.1⁻¹ * Real.sqrt sigma * Real.rpow 3 s1.1 * E * S +
      C.toReal * Real.rpow smid.1 (-(9 / 2 : ℝ)) *
        (s2.1 - smid.1)⁻¹ *
        (1 + (Real.rpow 3 (s1.1 / 2) * E) ^ 2) *
        Real.rpow 3 (s2.1 * (((n : ℤ) - 3 : ℤ) : ℝ)) * D)
  have hfirst :
      (Section6Dirichlet.dirichletSpectralReadoutConstant smid d).toReal *
          (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
            (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
              ((n : ℤ) - 3)).toReal) ≤
        (Section6Dirichlet.dirichletSpectralReadoutConstant smid d).toReal *
          centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ * R := by
    calc
      _ ≤ (Section6Dirichlet.dirichletSpectralReadoutConstant smid d).toReal *
          (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ * R) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa only [R] using hbudget)
            (mul_nonneg hscale hinv)) ENNReal.toReal_nonneg
      _ = _ := by ring
  simpa only [R] using add_le_add hfirst (le_refl
    (unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
      (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g)))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
