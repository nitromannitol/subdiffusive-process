module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHeadlineCellError
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepEllipticityFactorMoment

@[expose] public section

/-!
# High-cutoff ellipticity on the one-step source cell

This module isolates the deterministic part of
`l.one.step.upper` and `l.one.step.lower` and `l.one.step.upper` and `l.one.step.lower`: the literal upper and inverse
lower multiscale ellipticities of `a_L` on the source cell are controlled by
the Section 4 error observable normalized with `b_(L,n)`.  The remaining
work is purely the stochastic moment estimate for that error and its random
normalization.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem cutoff_family_LambdaSq_eq_at
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (s : ℝ) (omega : Sample d) :
    Ch04.LambdaSqCoeffField Q s (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch02.LambdaSq Q s (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  unfold Ch04.LambdaSqCoeffField
  rw [dite_eq_left hlocal]
  exact Ch02.LambdaSq_eq_ofAEEq
    (by simpa using aCutoff_canonicalFamily_aeeq M L omega) Q s (.finite 1)

private theorem cutoff_family_lambdaSq_eq_at
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (s : ℝ) (omega : Sample d) :
    Ch04.lambdaSqCoeffField Q s (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch02.lambdaSq Q s (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  unfold Ch04.lambdaSqCoeffField
  rw [dite_eq_left hlocal]
  exact Ch02.lambdaSq_eq_ofAEEq
    (by simpa using aCutoff_canonicalFamily_aeeq M L omega) Q s (.finite 1)

/-- Measurability of the full weighted descendant maximum.  This is the
countable-supremum companion to the individual random-normalization theorem
in `ResponseObservableMeasurability`. -/
theorem measurable_ellipticityMomentObservable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ) (s : ℝ) :
    Measurable (ellipticityMomentObservable M m n s) := by
  unfold ellipticityMomentObservable paperHomogenizationErrorDefault
    paperHomogenizationError paperHomogenizationErrorFinite
    paperScaleResponseAtScale paperMaxDescendantProbeAtScale
  simp only [one_div, ENNReal.rpow_one]
  apply Measurable.iSup
  intro L
  apply Measurable.iSup
  intro R
  norm_num
  apply Measurable.tsum
  intro l
  exact measurable_const.mul
    (ENNReal.continuous_rpow_const.measurable.comp
      (Measurable.iSup fun T ↦
        measurable_paperScalarProbeMaxOn_cutoff_randomNormalization M L.1
          (Ch02.cubeDomain T.1)
          (measurable_tailCoefficientCubeAverage M L.1 m)))

/-- The selected high-cutoff/source-cell paper error is one term of the
literal Section 4 ellipticity observable. -/
theorem sourceCell_paperError_le_ellipticityMomentObservable
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (j : ℕ) (hjn : j ≤ n) (s : ℝ) (omega : Sample d) :
    paperHomogenizationErrorDefault (originCube d (j : ℤ)) (j : ℤ) s
        .infinity (aCutoffFamily M (n + h) omega)
        (tailCoefficientCubeAverage M (n + h) n omega) ≤
      ellipticityMomentObservable M n (j : ℤ) s omega := by
  unfold ellipticityMomentObservable
  let L : {L : ℕ // n ≤ L} := ⟨n + h, Nat.le_add_right n h⟩
  let R : {R : TriadicCube d //
      R ∈ descendantsAtScale (originCube d (n : ℤ)) (j : ℤ)} :=
    ⟨originCube d (j : ℤ), originCube_mem_descendantsAtScale_of_nat_le hjn⟩
  exact le_iSup_of_le L (le_iSup_of_le R le_rfl)

/-- Parameterized upper ellipticity-root comparison.  The manuscript uses
`s = 1/4`; the source-scale aggregation first works at a smaller exponent and
then invokes antitonicity of `LambdaSq`. -/
theorem ofReal_sqrt_tailNormalized_highCutoffUpper_le_ellipticityMoment_of_s
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h j : ℕ) (hjn : j ≤ n) {s : ℝ} (hs : 0 < s)
    (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt
        ((tailCoefficientCubeAverage M (n + h) n omega)⁻¹ *
          Ch04.LambdaSqCoeffField (originCube d (j : ℤ)) s
            (.finite 1) (aCutoffRegCoeffField M (n + h) omega))) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        ellipticityMomentObservable M n (j : ℤ) s omega := by
  let Q := originCube d (j : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega
  let sigma := tailCoefficientCubeAverage M (n + h) n omega
  have hsigma : 0 < sigma := tailCoefficientCubeAverage_pos M (n + h) n omega
  have hroot :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_inv_mul_LambdaSq_le_one_add_sqrt_two_mul_error
      Q F hs hsigma
  have hcompare :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
      Q F (fun R ↦
        (aCutoffEnvelopeScalarTriadicCoeffData M (n + h) omega).onCube R
          |>.isSymmetric)
      hs hsigma
  rw [cutoff_family_LambdaSq_eq_at M (n + h) Q s omega]
  calc
    ENNReal.ofReal (Real.sqrt (sigma⁻¹ * Ch02.LambdaSq Q s
        (.finite 1) F)) ≤
        ENNReal.ofReal (1 + Real.sqrt 2 *
          Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
            (scalarMatrix (d := d) sigma)) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
            (scalarMatrix (d := d) sigma)) := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (mul_nonneg (Real.sqrt_nonneg 2)
            (Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q F _ hs)),
        ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
        paperHomogenizationErrorDefault Q Q.scale s .infinity F sigma := by
      gcongr
    _ ≤ _ := by
      have hscale : Q.scale = (j : ℤ) := by simp [Q, originCube]
      rw [hscale]
      dsimp only [Q, F, sigma]
      gcongr
      exact sourceCell_paperError_le_ellipticityMomentObservable
        M n h j hjn s omega

/-- Parameterized inverse-lower twin of the high-cutoff comparison. -/
theorem ofReal_sqrt_tailNormalized_highCutoffLowerInv_le_ellipticityMoment_of_s
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h j : ℕ) (hjn : j ≤ n) {s : ℝ} (hs : 0 < s)
    (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt
        (tailCoefficientCubeAverage M (n + h) n omega *
          (Ch04.lambdaSqCoeffField (originCube d (j : ℤ)) s
            (.finite 1) (aCutoffRegCoeffField M (n + h) omega))⁻¹)) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        ellipticityMomentObservable M n (j : ℤ) s omega := by
  let Q := originCube d (j : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega
  let sigma := tailCoefficientCubeAverage M (n + h) n omega
  have hsigma : 0 < sigma := tailCoefficientCubeAverage_pos M (n + h) n omega
  have hroot :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_mul_lambdaSq_inv_le_one_add_sqrt_two_mul_error
      Q F hs hsigma
  have hcompare :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
      Q F (fun R ↦
        (aCutoffEnvelopeScalarTriadicCoeffData M (n + h) omega).onCube R
          |>.isSymmetric)
      hs hsigma
  rw [cutoff_family_lambdaSq_eq_at M (n + h) Q s omega]
  calc
    ENNReal.ofReal (Real.sqrt (sigma * (Ch02.lambdaSq Q s
        (.finite 1) F)⁻¹)) ≤
        ENNReal.ofReal (1 + Real.sqrt 2 *
          Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
            (scalarMatrix (d := d) sigma)) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
            (scalarMatrix (d := d) sigma)) := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (mul_nonneg (Real.sqrt_nonneg 2)
            (Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q F _ hs)),
        ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
        paperHomogenizationErrorDefault Q Q.scale s .infinity F sigma := by
      gcongr
    _ ≤ _ := by
      have hscale : Q.scale = (j : ℤ) := by simp [Q, originCube]
      rw [hscale]
      dsimp only [Q, F, sigma]
      gcongr
      exact sourceCell_paperError_le_ellipticityMomentObservable
        M n h j hjn s omega

/-- A smaller positive aggregation exponent controls the manuscript's upper
`s = 1/4` factor by antitonicity of `LambdaSq`. -/
theorem ofReal_sqrt_tailNormalized_highCutoffUpper_quarter_le_of_s
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h j : ℕ) (hjn : j ≤ n) {s : ℝ} (hs : 0 < s)
    (hsq : s < 1 / 4) (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt
        ((tailCoefficientCubeAverage M (n + h) n omega)⁻¹ *
          Ch04.LambdaSqCoeffField (originCube d (j : ℤ)) (1 / 4)
            (.finite 1) (aCutoffRegCoeffField M (n + h) omega))) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        ellipticityMomentObservable M n (j : ℤ) s omega := by
  let Q := originCube d (j : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega
  have hmono :
      Ch04.LambdaSqCoeffField Q (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M (n + h) omega) ≤
        Ch04.LambdaSqCoeffField Q s (.finite 1)
          (aCutoffRegCoeffField M (n + h) omega) := by
    rw [cutoff_family_LambdaSq_eq_at M (n + h) Q (1 / 4) omega,
      cutoff_family_LambdaSq_eq_at M (n + h) Q s omega]
    exact Ch02.LambdaSq_finite_antitone Q F hs hsq (by norm_num)
  have hfactor0 :
      0 ≤ (tailCoefficientCubeAverage M (n + h) n omega)⁻¹ :=
    inv_nonneg.mpr (tailCoefficientCubeAverage_pos M (n + h) n omega).le
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt
        ((tailCoefficientCubeAverage M (n + h) n omega)⁻¹ *
          Ch04.LambdaSqCoeffField Q s (.finite 1)
            (aCutoffRegCoeffField M (n + h) omega))) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmono hfactor0)
    _ ≤ _ := by
      exact ofReal_sqrt_tailNormalized_highCutoffUpper_le_ellipticityMoment_of_s
        M n h j hjn hs omega

/-- A smaller positive aggregation exponent controls the manuscript's
inverse-lower `s = 1/4` factor. -/
theorem ofReal_sqrt_tailNormalized_highCutoffLowerInv_quarter_le_of_s
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h j : ℕ) (hjn : j ≤ n) {s : ℝ} (hs : 0 < s)
    (hsq : s < 1 / 4) (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt
        (tailCoefficientCubeAverage M (n + h) n omega *
          (Ch04.lambdaSqCoeffField (originCube d (j : ℤ)) (1 / 4)
            (.finite 1) (aCutoffRegCoeffField M (n + h) omega))⁻¹)) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        ellipticityMomentObservable M n (j : ℤ) s omega := by
  let Q := originCube d (j : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega
  have hmono :
      Ch04.lambdaSqCoeffField Q s (.finite 1)
          (aCutoffRegCoeffField M (n + h) omega) ≤
        Ch04.lambdaSqCoeffField Q (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M (n + h) omega) := by
    rw [cutoff_family_lambdaSq_eq_at M (n + h) Q s omega,
      cutoff_family_lambdaSq_eq_at M (n + h) Q (1 / 4) omega]
    exact Ch02.lambdaSq_finite_mono Q F hs hsq (by norm_num)
  have hlowerPos : 0 < Ch04.lambdaSqCoeffField Q s (.finite 1)
      (aCutoffRegCoeffField M (n + h) omega) := by
    rw [cutoff_family_lambdaSq_eq_at M (n + h) Q s omega]
    exact Ch02.lambdaSq_finite_pos Q F hs (by norm_num)
  have hinv :
      (Ch04.lambdaSqCoeffField Q (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M (n + h) omega))⁻¹ ≤
        (Ch04.lambdaSqCoeffField Q s (.finite 1)
          (aCutoffRegCoeffField M (n + h) omega))⁻¹ :=
    inv_anti₀ hlowerPos hmono
  have htail0 : 0 ≤ tailCoefficientCubeAverage M (n + h) n omega :=
    (tailCoefficientCubeAverage_pos M (n + h) n omega).le
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt
        (tailCoefficientCubeAverage M (n + h) n omega *
          (Ch04.lambdaSqCoeffField Q s (.finite 1)
            (aCutoffRegCoeffField M (n + h) omega))⁻¹)) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hinv htail0)
    _ ≤ _ := by
      exact ofReal_sqrt_tailNormalized_highCutoffLowerInv_le_ellipticityMoment_of_s
        M n h j hjn hs omega

/-- Pointwise upper ellipticity-root comparison at the high cutoff, with the
random tail normalization used in the printed proof. -/
theorem ofReal_sqrt_tailNormalized_highCutoffUpper_le_ellipticityMoment
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h j : ℕ) (hjn : j ≤ n) (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt
        ((tailCoefficientCubeAverage M (n + h) n omega)⁻¹ *
          Ch04.LambdaSqCoeffField (originCube d (j : ℤ)) (1 / 4)
            (.finite 1) (aCutoffRegCoeffField M (n + h) omega))) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        ellipticityMomentObservable M n (j : ℤ) (1 / 4) omega := by
  let Q := originCube d (j : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega
  let sigma := tailCoefficientCubeAverage M (n + h) n omega
  have hsigma : 0 < sigma := tailCoefficientCubeAverage_pos M (n + h) n omega
  have hroot :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_inv_mul_LambdaSq_le_one_add_sqrt_two_mul_error
      Q F (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  have hcompare :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
      Q F (fun R ↦
        (aCutoffEnvelopeScalarTriadicCoeffData M (n + h) omega).onCube R
          |>.isSymmetric)
      (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  rw [cutoff_family_LambdaSq_eq_at M (n + h) Q (1 / 4) omega]
  calc
    ENNReal.ofReal (Real.sqrt (sigma⁻¹ * Ch02.LambdaSq Q (1 / 4)
        (.finite 1) F)) ≤
        ENNReal.ofReal (1 + Real.sqrt 2 *
          Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
            (scalarMatrix (d := d) sigma)) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
            (scalarMatrix (d := d) sigma)) := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (mul_nonneg (Real.sqrt_nonneg 2)
            (Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q F _
              (by norm_num : (0 : ℝ) < 1 / 4))),
        ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
        paperHomogenizationErrorDefault Q Q.scale (1 / 4) .infinity F sigma := by
      gcongr
    _ ≤ _ := by
      have hscale : Q.scale = (j : ℤ) := by simp [Q, originCube]
      rw [hscale]
      dsimp only [Q, F, sigma]
      gcongr
      exact sourceCell_paperError_le_ellipticityMomentObservable
        M n h j hjn (1 / 4) omega

/-- Pointwise inverse-lower twin of the high-cutoff comparison. -/
theorem ofReal_sqrt_tailNormalized_highCutoffLowerInv_le_ellipticityMoment
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h j : ℕ) (hjn : j ≤ n) (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt
        (tailCoefficientCubeAverage M (n + h) n omega *
          (Ch04.lambdaSqCoeffField (originCube d (j : ℤ)) (1 / 4)
            (.finite 1) (aCutoffRegCoeffField M (n + h) omega))⁻¹)) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        ellipticityMomentObservable M n (j : ℤ) (1 / 4) omega := by
  let Q := originCube d (j : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega
  let sigma := tailCoefficientCubeAverage M (n + h) n omega
  have hsigma : 0 < sigma := tailCoefficientCubeAverage_pos M (n + h) n omega
  have hroot :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_mul_lambdaSq_inv_le_one_add_sqrt_two_mul_error
      Q F (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  have hcompare :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
      Q F (fun R ↦
        (aCutoffEnvelopeScalarTriadicCoeffData M (n + h) omega).onCube R
          |>.isSymmetric)
      (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  rw [cutoff_family_lambdaSq_eq_at M (n + h) Q (1 / 4) omega]
  calc
    ENNReal.ofReal (Real.sqrt (sigma * (Ch02.lambdaSq Q (1 / 4)
        (.finite 1) F)⁻¹)) ≤
        ENNReal.ofReal (1 + Real.sqrt 2 *
          Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
            (scalarMatrix (d := d) sigma)) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
            (scalarMatrix (d := d) sigma)) := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (mul_nonneg (Real.sqrt_nonneg 2)
            (Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q F _
              (by norm_num : (0 : ℝ) < 1 / 4))),
        ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
        paperHomogenizationErrorDefault Q Q.scale (1 / 4) .infinity F sigma := by
      gcongr
    _ ≤ _ := by
      have hscale : Q.scale = (j : ℤ) := by simp [Q, originCube]
      rw [hscale]
      dsimp only [Q, F, sigma]
      gcongr
      exact sourceCell_paperError_le_ellipticityMomentObservable
        M n h j hjn (1 / 4) omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
