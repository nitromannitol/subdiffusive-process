module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpTwoBlockMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CombineAssemblySeams
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SecondMomentBudgets
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentFactorization

@[expose] public section

/-!
# Second moments of the one-step coarse-Poincare factors

This module converts the sharp `q = 1` square-root comparison into the
moment interface used.
The comparison is pointwise; the only stochastic input retained by the final
bound is the paper homogenization-error moment.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem cutoff_family_LambdaSq_eq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch02.LambdaSq (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  unfold Ch04.LambdaSqCoeffField
  rw [dite_eq_left hlocal]
  exact Ch02.LambdaSq_eq_ofAEEq
    (by simpa using! aCutoff_canonicalFamily_aeeq M L omega)
    (originCube d (m : ℤ)) (1 / 4) (.finite 1)

private theorem cutoff_family_lambdaSq_eq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  unfold Ch04.lambdaSqCoeffField
  rw [dite_eq_left hlocal]
  exact Ch02.lambdaSq_eq_ofAEEq
    (by simpa using! aCutoff_canonicalFamily_aeeq M L omega)
    (originCube d (m : ℤ)) (1 / 4) (.finite 1)

private theorem cutoff_paperError_eq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega =
      paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) (1 / 4)
        .infinity (.finite 1) (aCutoffEnvelopeTriadicCoeffFamily M L omega)
          (ahom M L) := by
  have htranslate : translatePotentialSample (0 : Vec d) omega = omega := by
    funext k
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro x
    change omega k (x + 0) = omega k x
    rw [add_zero]
  unfold translatedHomogenizationErrorRandom
  rw [htranslate]
  simpa [aCutoffFamily, aCutoffEnvelopeTriadicCoeffFamily] using!
    (paperHomogenizationError_toTriadicCoeffFamily_eq
      (aCutoffTriadicData M L omega)
      (aCutoffEnvelopeScalarTriadicCoeffData M L omega)
      (originCube d (m : ℤ)) (m : ℤ) (1 / 4) .infinity (.finite 1)
      (ahom M L))

/-- Pointwise upper-factor comparison in the literal paper-error carrier. -/
theorem ofReal_sqrt_normalized_cutoffUpper_le_one_add_sqrt_two_mul_error
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt ((ahom M L)⁻¹ *
        Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega))) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega := by
  let Q := originCube d (m : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M L omega
  have hsigma : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hroot :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_inv_mul_LambdaSq_le_one_add_sqrt_two_mul_error
        Q F (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  have hcompare :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
        Q F (fun R ↦
          (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube R
            |>.isSymmetric)
        (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  rw [cutoff_family_LambdaSq_eq M L m omega]
  calc
    ENNReal.ofReal (Real.sqrt ((ahom M L)⁻¹ *
        Ch02.LambdaSq Q (1 / 4) (.finite 1) F)) ≤
        ENNReal.ofReal (1 + Real.sqrt 2 *
          Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
            (scalarMatrix (d := d) (ahom M L))) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
            (scalarMatrix (d := d) (ahom M L))) := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (mul_nonneg (Real.sqrt_nonneg 2)
          (Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q F _
            (by norm_num : (0 : ℝ) < 1 / 4))),
        ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
        paperHomogenizationError Q Q.scale (1 / 4) .infinity (.finite 1) F
          (ahom M L) := by gcongr
    _ = _ := by
      rw [show Q.scale = (m : ℤ) by simp [Q, originCube],
        ← cutoff_paperError_eq M L m omega]

/-- Pointwise lower-factor counterpart. -/
theorem ofReal_sqrt_normalized_cutoffLowerInv_le_one_add_sqrt_two_mul_error
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt (ahom M L *
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega))⁻¹)) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega := by
  let Q := originCube d (m : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M L omega
  have hsigma : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hroot :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_mul_lambdaSq_inv_le_one_add_sqrt_two_mul_error
        Q F (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  have hcompare :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
        Q F (fun R ↦
          (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube R
            |>.isSymmetric)
        (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  rw [cutoff_family_lambdaSq_eq M L m omega]
  calc
    ENNReal.ofReal (Real.sqrt (ahom M L *
        (Ch02.lambdaSq Q (1 / 4) (.finite 1) F)⁻¹)) ≤
        ENNReal.ofReal (1 + Real.sqrt 2 *
          Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
            (scalarMatrix (d := d) (ahom M L))) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
            (scalarMatrix (d := d) (ahom M L))) := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (mul_nonneg (Real.sqrt_nonneg 2)
          (Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q F _
            (by norm_num : (0 : ℝ) < 1 / 4))),
        ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
        paperHomogenizationError Q Q.scale (1 / 4) .infinity (.finite 1) F
          (ahom M L) := by gcongr
    _ = _ := by
      rw [show Q.scale = (m : ℤ) by simp [Q, originCube],
        ← cutoff_paperError_eq M L m omega]

/-- A pointwise `1 + c E` comparison gives the corresponding paper `L^p`
bound on a probability space. -/
theorem paperENNRealLpNorm_le_one_add_const_mul_of_pointwise
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {p : ℝ} (hp : 1 ≤ p) {X E : Omega → ℝ≥0∞} (c : ℝ≥0∞)
    (hE : Measurable E)
    (hpoint : ∀ omega, X omega ≤ 1 + c * E omega) :
    paperENNRealLpNorm mu p X ≤
      1 + c * paperENNRealLpNorm mu p E := by
  have hmono := paperENNRealLpNorm_mono_ae mu (zero_le_one.trans hp)
    (Filter.Eventually.of_forall hpoint)
  have hadd := paperENNRealLpNorm_add_le mu hp
    (measurable_const : Measurable (fun _ : Omega ↦ (1 : ℝ≥0∞))).aemeasurable
    (hE.const_mul c).aemeasurable
  calc
    paperENNRealLpNorm mu p X ≤
        paperENNRealLpNorm mu p (fun omega ↦ 1 + c * E omega) := hmono
    _ ≤ paperENNRealLpNorm mu p (fun _omega ↦ 1) +
          paperENNRealLpNorm mu p (fun omega ↦ c * E omega) := hadd
    _ = 1 + c * paperENNRealLpNorm mu p E := by
      rw [paperENNRealLpNorm_one,
        paperENNRealLpNorm_const_mul_eq mu (zero_lt_one.trans_le hp) c E hE]

/-- `L^p` control of the normalized upper square root by the literal paper
error. -/
theorem paperENNRealLpNorm_normalized_cutoffUpper_root_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    {p : ℝ} (hp : 1 ≤ p) :
    paperENNRealLpNorm M.P.toMeasure p (fun omega ↦
        ENNReal.ofReal (Real.sqrt ((ahom M L)⁻¹ *
          Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
            (aCutoffRegCoeffField M L omega)))) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        paperENNRealLpNorm M.P.toMeasure p
          (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) := by
  apply paperENNRealLpNorm_le_one_add_const_mul_of_pointwise
    M.P.toMeasure hp (ENNReal.ofReal (Real.sqrt 2))
    (SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.measurable_translatedHomogenizationErrorRandom_quarter_one M L m)
  exact ofReal_sqrt_normalized_cutoffUpper_le_one_add_sqrt_two_mul_error M L m

/-- `L^p` control of the normalized inverse lower square root. -/
theorem paperENNRealLpNorm_normalized_cutoffLowerInv_root_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    {p : ℝ} (hp : 1 ≤ p) :
    paperENNRealLpNorm M.P.toMeasure p (fun omega ↦
        ENNReal.ofReal (Real.sqrt (ahom M L *
          (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
            (aCutoffRegCoeffField M L omega))⁻¹))) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        paperENNRealLpNorm M.P.toMeasure p
          (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) := by
  apply paperENNRealLpNorm_le_one_add_const_mul_of_pointwise
    M.P.toMeasure hp (ENNReal.ofReal (Real.sqrt 2))
    (SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.measurable_translatedHomogenizationErrorRandom_quarter_one M L m)
  exact ofReal_sqrt_normalized_cutoffLowerInv_le_one_add_sqrt_two_mul_error M L m

/-- Squaring an `ENNReal` observable doubles its paper-moment exponent. -/
theorem paperENNRealLpNorm_sq
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p (fun omega => X omega ^ (2 : ℕ)) =
      (paperENNRealLpNorm mu (2 * p) X) ^ (2 : ℕ) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d131_paperENNRealLpNorm_sq (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X)

theorem paperENNRealLpNorm_congr_ae
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (p : ℝ) {X Y : Omega → ℝ≥0∞} (hXY : X =ᵐ[mu] Y) :
    paperENNRealLpNorm mu p X = paperENNRealLpNorm mu p Y := by
  unfold paperENNRealLpNorm
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hXY] with omega homega
  rw [homega]

/-- Convert a finite paper `L²` bound for a nonnegative real observable into
the exact Bochner-integrability and real second-moment pair consumed by the
finite-cell Holder fold. -/
theorem integrable_sq_and_integral_sq_le_of_paperENNRealLpNorm_two
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {X : Omega → ℝ} (hX : Measurable X) (hX0 : ∀ omega, 0 ≤ X omega)
    {L : ℝ} (hL : 0 ≤ L)
    (hnorm : paperENNRealLpNorm mu 2 (fun omega ↦ ENNReal.ofReal (X omega)) ≤
      ENNReal.ofReal L) :
    Integrable (fun omega ↦ X omega ^ 2) mu ∧
      ∫ omega, X omega ^ 2 ∂mu ≤ L ^ 2 := by
  let Y : Omega → ℝ≥0∞ := fun omega ↦ ENNReal.ofReal (X omega)
  have hYtop : ∀ omega, Y omega ≠ ∞ := fun _ ↦ ENNReal.ofReal_ne_top
  have hLp : eLpNorm X 2 mu ≤ ENNReal.ofReal L := by
    have hbridge :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.paperENNRealLpNorm_eq_eLpNorm_toReal
        mu (by norm_num : (0 : ℝ) < 2) hYtop
    have htoReal : (fun omega ↦ (Y omega).toReal) = X := by
      funext omega
      exact ENNReal.toReal_ofReal (hX0 omega)
    rw [htoReal] at hbridge
    change paperENNRealLpNorm mu 2 Y ≤ ENNReal.ofReal L at hnorm
    rw [hbridge] at hnorm
    norm_num at hnorm
    simpa only [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hX.aestronglyMeasurable] using! hnorm
  have hmem : MemLp X 2 mu := hLp.trans_lt ENNReal.ofReal_lt_top
  have hint : Integrable (fun omega ↦ X omega ^ 2) mu := by
    exact (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hmem
  refine ⟨hint, ?_⟩
  rw [← Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hmem]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hLp
  rw [ENNReal.toReal_ofReal hL] at hreal
  exact (sq_le_sq₀ ENNReal.toReal_nonneg hL).2 hreal

/-- AE-nonnegative variant of the paper-`L²` conversion.  This is the form
needed for measurable representatives of coefficient extrema: the literal
extremum is nonnegative, while `AEMeasurable.mk` only agrees with it almost
everywhere. -/
theorem integrable_sq_and_integral_sq_le_of_paperENNRealLpNorm_two_of_ae_nonneg
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {X : Omega → ℝ} (hX : Measurable X)
    (hX0 : ∀ᵐ omega ∂mu, 0 ≤ X omega)
    {L : ℝ} (hL : 0 ≤ L)
    (hnorm : paperENNRealLpNorm mu 2 (fun omega ↦ ENNReal.ofReal (X omega)) ≤
      ENNReal.ofReal L) :
    Integrable (fun omega ↦ X omega ^ 2) mu ∧
      ∫ omega, X omega ^ 2 ∂mu ≤ L ^ 2 := by
  let Xp : Omega → ℝ := fun omega ↦ max (X omega) 0
  have hXp : Measurable Xp := hX.max measurable_const
  have hXp0 : ∀ omega, 0 ≤ Xp omega := fun omega ↦ le_max_right _ _
  have hnormp : paperENNRealLpNorm mu 2
      (fun omega ↦ ENNReal.ofReal (Xp omega)) ≤ ENNReal.ofReal L := by
    have hfun : (fun omega ↦ ENNReal.ofReal (Xp omega)) =
        fun omega ↦ ENNReal.ofReal (X omega) := by
      funext omega
      simp only [Xp, ENNReal.ofReal_max, ENNReal.ofReal_zero]
      exact max_eq_left (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (X omega))
    rwa [hfun]
  obtain ⟨hintp, hboundp⟩ :=
    integrable_sq_and_integral_sq_le_of_paperENNRealLpNorm_two
      mu hXp hXp0 hL hnormp
  have heq : (fun omega ↦ X omega ^ 2) =ᵐ[mu]
      fun omega ↦ Xp omega ^ 2 := by
    filter_upwards [hX0] with omega homega
    simp only [Xp, max_eq_left homega]
  exact ⟨hintp.congr heq.symm,
    (integral_congr_ae heq).trans_le hboundp⟩

/-- Nonnegative measurable representative of the upper ratio
`ahom_L⁻¹ LambdaSq`. -/
noncomputable def oneStepUpperEllipticityRatioMeasurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) : Sample d → ℝ :=
  fun omega ↦ max ((ahom M L)⁻¹ *
    SubdiffusiveProcess.CoarseGrainingVocab.cutoffUpperEllipticityMeasurable M L m omega) 0

/-- Nonnegative measurable representative of the lower inverse ratio
`ahom_L lambdaSq⁻¹`. -/
noncomputable def oneStepLowerInvEllipticityRatioMeasurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) : Sample d → ℝ :=
  fun omega ↦ max (ahom M L *
    (SubdiffusiveProcess.CoarseGrainingVocab.cutoffLowerEllipticityMeasurable M L m omega)⁻¹) 0

theorem measurable_oneStepUpperEllipticityRatioMeasurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    Measurable (oneStepUpperEllipticityRatioMeasurable M L m) := by
  exact ((SubdiffusiveProcess.CoarseGrainingVocab.measurable_cutoffUpperEllipticityMeasurable
    M L m).const_mul _).max measurable_const

theorem measurable_oneStepLowerInvEllipticityRatioMeasurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    Measurable (oneStepLowerInvEllipticityRatioMeasurable M L m) := by
  exact ((SubdiffusiveProcess.CoarseGrainingVocab.measurable_cutoffLowerEllipticityMeasurable
    M L m).inv.const_mul _).max measurable_const

theorem oneStepUpperEllipticityRatioMeasurable_ae_eq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    oneStepUpperEllipticityRatioMeasurable M L m =ᵐ[M.P.toMeasure]
      fun omega ↦ (ahom M L)⁻¹ *
        Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) := by
  filter_upwards [SubdiffusiveProcess.CoarseGrainingVocab.cutoffUpperEllipticityMeasurable_ae_eq
    M L m] with omega heq
  rw [oneStepUpperEllipticityRatioMeasurable, heq, max_eq_left]
  exact mul_nonneg (inv_nonneg.mpr ((Real.exp_pos _).trans_le
    (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)).le)
    (Ch04.LambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num))

theorem oneStepLowerInvEllipticityRatioMeasurable_ae_eq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    oneStepLowerInvEllipticityRatioMeasurable M L m =ᵐ[M.P.toMeasure]
      fun omega ↦ ahom M L *
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega))⁻¹ := by
  filter_upwards [SubdiffusiveProcess.CoarseGrainingVocab.cutoffLowerEllipticityMeasurable_ae_eq
    M L m] with omega heq
  rw [oneStepLowerInvEllipticityRatioMeasurable, heq, max_eq_left]
  exact mul_nonneg ((Real.exp_pos _).trans_le
    (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)).le
    (inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num)))

/-- The normalized upper ellipticity ratio has a second moment controlled by
the fourth moment of the literal paper error. -/
theorem paperENNRealLpNorm_normalized_cutoffUpper_ratio_two_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (R : ℝ≥0∞)
    (herror : paperENNRealLpNorm M.P.toMeasure 4
        (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) ≤ R) :
    paperENNRealLpNorm M.P.toMeasure 2 (fun omega ↦
        ENNReal.ofReal ((ahom M L)⁻¹ *
          Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
            (aCutoffRegCoeffField M L omega))) ≤
      (1 + ENNReal.ofReal (Real.sqrt 2) * R) ^ (2 : ℕ) := by
  let X : Sample d → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (Real.sqrt ((ahom M L)⁻¹ *
      Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega)))
  have hratio : (fun omega : Sample d ↦
      ENNReal.ofReal ((ahom M L)⁻¹ *
        Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega))) =
      fun omega ↦ X omega ^ (2 : ℕ) := by
    funext omega
    have hnonneg : 0 ≤ (ahom M L)⁻¹ *
        Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) :=
      mul_nonneg (inv_nonneg.mpr ((Real.exp_pos _).trans_le
        (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)).le)
        (Ch04.LambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num))
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]
  rw [hratio, paperENNRealLpNorm_sq M.P.toMeasure (by norm_num) X]
  have hroot := paperENNRealLpNorm_normalized_cutoffUpper_root_le
    M L m (by norm_num : (1 : ℝ) ≤ 4)
  have hroot' : paperENNRealLpNorm M.P.toMeasure 4 X ≤
      1 + ENNReal.ofReal (Real.sqrt 2) * R := by
    have hx : paperENNRealLpNorm M.P.toMeasure 4 X ≤
        1 + ENNReal.ofReal (Real.sqrt 2) *
          paperENNRealLpNorm M.P.toMeasure 4
            (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) := by
      simpa only [X] using! hroot
    exact hx.trans (by gcongr)
  norm_num at hroot' ⊢
  exact pow_le_pow_left' hroot' 2

/-- The inverse normalized lower ellipticity ratio obeys the same second-
moment budget. -/
theorem paperENNRealLpNorm_normalized_cutoffLowerInv_ratio_two_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (R : ℝ≥0∞)
    (herror : paperENNRealLpNorm M.P.toMeasure 4
        (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) ≤ R) :
    paperENNRealLpNorm M.P.toMeasure 2 (fun omega ↦
        ENNReal.ofReal (ahom M L *
          (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
            (aCutoffRegCoeffField M L omega))⁻¹)) ≤
      (1 + ENNReal.ofReal (Real.sqrt 2) * R) ^ (2 : ℕ) := by
  let X : Sample d → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (Real.sqrt (ahom M L *
      (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega))⁻¹))
  have hratio : (fun omega : Sample d ↦
      ENNReal.ofReal (ahom M L *
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega))⁻¹)) =
      fun omega ↦ X omega ^ (2 : ℕ) := by
    funext omega
    have hnonneg : 0 ≤ ahom M L *
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega))⁻¹ :=
      mul_nonneg ((Real.exp_pos _).trans_le
        (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)).le
        (inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num)))
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]
  rw [hratio, paperENNRealLpNorm_sq M.P.toMeasure (by norm_num) X]
  have hroot := paperENNRealLpNorm_normalized_cutoffLowerInv_root_le
    M L m (by norm_num : (1 : ℝ) ≤ 4)
  have hroot' : paperENNRealLpNorm M.P.toMeasure 4 X ≤
      1 + ENNReal.ofReal (Real.sqrt 2) * R := by
    have hx : paperENNRealLpNorm M.P.toMeasure 4 X ≤
        1 + ENNReal.ofReal (Real.sqrt 2) *
          paperENNRealLpNorm M.P.toMeasure 4
            (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) := by
      simpa only [X] using! hroot
    exact hx.trans (by gcongr)
  norm_num at hroot' ⊢
  exact pow_le_pow_left' hroot' 2

/-- Real second-moment budget for the measurable upper ratio.  This is the
literal integrability interface required before multiplying back by the
deterministic `ahom_L` and Poincare-discount factors. -/
theorem integrable_sq_and_integral_sq_oneStepUpperEllipticityRatioMeasurable_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (herror : paperENNRealLpNorm M.P.toMeasure 4
        (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) ≤
      ENNReal.ofReal R) :
    Integrable (fun omega ↦
        oneStepUpperEllipticityRatioMeasurable M L m omega ^ 2)
        M.P.toMeasure ∧
      ∫ omega, oneStepUpperEllipticityRatioMeasurable M L m omega ^ 2
          ∂M.P.toMeasure ≤
        ((1 + Real.sqrt 2 * R) ^ 2) ^ 2 := by
  let X := oneStepUpperEllipticityRatioMeasurable M L m
  let L2 : ℝ := (1 + Real.sqrt 2 * R) ^ 2
  have hnormLiteral := paperENNRealLpNorm_normalized_cutoffUpper_ratio_two_le
    M L m (ENNReal.ofReal R) herror
  have hae : (fun omega : Sample d ↦ ENNReal.ofReal (X omega)) =ᵐ[M.P.toMeasure]
      fun omega ↦ ENNReal.ofReal ((ahom M L)⁻¹ *
        Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega)) := by
    filter_upwards [oneStepUpperEllipticityRatioMeasurable_ae_eq M L m]
      with omega heq
    exact congrArg ENNReal.ofReal heq
  have hnorm : paperENNRealLpNorm M.P.toMeasure 2
      (fun omega ↦ ENNReal.ofReal (X omega)) ≤ ENNReal.ofReal L2 := by
    rw [paperENNRealLpNorm_congr_ae M.P.toMeasure 2 hae]
    refine hnormLiteral.trans ?_
    dsimp only [L2]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (Real.sqrt_nonneg 2) hR),
      ← ENNReal.ofReal_pow
        (add_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg 2) hR))]
  exact integrable_sq_and_integral_sq_le_of_paperENNRealLpNorm_two
    M.P.toMeasure (measurable_oneStepUpperEllipticityRatioMeasurable M L m)
      (fun omega ↦ le_max_right _ _) (sq_nonneg _) hnorm

/-- Real second-moment budget for the measurable inverse lower ratio. -/
theorem integrable_sq_and_integral_sq_oneStepLowerInvEllipticityRatioMeasurable_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (herror : paperENNRealLpNorm M.P.toMeasure 4
        (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) ≤
      ENNReal.ofReal R) :
    Integrable (fun omega ↦
        oneStepLowerInvEllipticityRatioMeasurable M L m omega ^ 2)
        M.P.toMeasure ∧
      ∫ omega, oneStepLowerInvEllipticityRatioMeasurable M L m omega ^ 2
          ∂M.P.toMeasure ≤
        ((1 + Real.sqrt 2 * R) ^ 2) ^ 2 := by
  let X := oneStepLowerInvEllipticityRatioMeasurable M L m
  let L2 : ℝ := (1 + Real.sqrt 2 * R) ^ 2
  have hnormLiteral :=
    paperENNRealLpNorm_normalized_cutoffLowerInv_ratio_two_le
      M L m (ENNReal.ofReal R) herror
  have hae : (fun omega : Sample d ↦ ENNReal.ofReal (X omega)) =ᵐ[M.P.toMeasure]
      fun omega ↦ ENNReal.ofReal (ahom M L *
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega))⁻¹) := by
    filter_upwards [oneStepLowerInvEllipticityRatioMeasurable_ae_eq M L m]
      with omega heq
    exact congrArg ENNReal.ofReal heq
  have hnorm : paperENNRealLpNorm M.P.toMeasure 2
      (fun omega ↦ ENNReal.ofReal (X omega)) ≤ ENNReal.ofReal L2 := by
    rw [paperENNRealLpNorm_congr_ae M.P.toMeasure 2 hae]
    refine hnormLiteral.trans ?_
    dsimp only [L2]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (Real.sqrt_nonneg 2) hR),
      ← ENNReal.ofReal_pow
        (add_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg 2) hR))]
  exact integrable_sq_and_integral_sq_le_of_paperENNRealLpNorm_two
    M.P.toMeasure (measurable_oneStepLowerInvEllipticityRatioMeasurable M L m)
      (fun omega ↦ le_max_right _ _) (sq_nonneg _) hnorm

/-- Measurable representative of the squared upper coarse-Poincare factor. -/
noncomputable def oneStepUpperPoincareEnergyFactorMeasurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) : Sample d → ℝ :=
  fun omega ↦
    Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) ^ 2 * ahom M L *
      oneStepUpperEllipticityRatioMeasurable M L m omega

/-- Measurable representative of the squared lower coarse-Poincare factor. -/
noncomputable def oneStepLowerPoincareEnergyFactorMeasurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) : Sample d → ℝ :=
  fun omega ↦
    Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) ^ 2 *
      (ahom M L)⁻¹ * oneStepLowerInvEllipticityRatioMeasurable M L m omega

theorem measurable_oneStepUpperPoincareEnergyFactorMeasurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    Measurable (oneStepUpperPoincareEnergyFactorMeasurable M L m) :=
  (measurable_oneStepUpperEllipticityRatioMeasurable M L m).const_mul _

theorem measurable_oneStepLowerPoincareEnergyFactorMeasurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    Measurable (oneStepLowerPoincareEnergyFactorMeasurable M L m) :=
  (measurable_oneStepLowerInvEllipticityRatioMeasurable M L m).const_mul _

/-- The measurable upper representative agrees almost surely with the exact
squared factor in `oneStep_dirichletCell_energy_le_poincare_quarter`. -/
theorem oneStepUpperPoincareEnergyFactorMeasurable_ae_eq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    oneStepUpperPoincareEnergyFactorMeasurable M L m =ᵐ[M.P.toMeasure]
      fun omega ↦
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor (originCube d (m : ℤ))
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4) (.finite 1)) ^ 2 := by
  filter_upwards [oneStepUpperEllipticityRatioMeasurable_ae_eq M L m]
    with omega heq
  rw [oneStepUpperPoincareEnergyFactorMeasurable, heq,
    cutoff_family_LambdaSq_eq M L m omega]
  have hsigma : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  unfold Ch03.poincareUpperEllipticityFactor
  have hrpow : Real.rpow
      (Ch02.LambdaSq (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)) (1 / 2 : ℝ) =
      Real.sqrt (Ch02.LambdaSq (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)) := by
    simpa only [Real.instPow] using!
      (Real.sqrt_eq_rpow (Ch02.LambdaSq (originCube d (m : ℤ)) (1 / 4)
        (.finite 1) (aCutoffEnvelopeTriadicCoeffFamily M L omega))).symm
  rw [hrpow, mul_pow,
    Real.sq_sqrt (Ch02.LambdaSq_finite_nonneg _ _ (by norm_num) (by norm_num))]
  field_simp

/-- The measurable lower representative agrees almost surely with the exact
squared factor in `oneStep_neumannCell_energy_le_poincare_quarter`. -/
theorem oneStepLowerPoincareEnergyFactorMeasurable_ae_eq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    oneStepLowerPoincareEnergyFactorMeasurable M L m =ᵐ[M.P.toMeasure]
      fun omega ↦
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor (originCube d (m : ℤ))
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4) (.finite 1)) ^ 2 := by
  filter_upwards [oneStepLowerInvEllipticityRatioMeasurable_ae_eq M L m]
    with omega heq
  rw [oneStepLowerPoincareEnergyFactorMeasurable, heq,
    cutoff_family_lambdaSq_eq M L m omega]
  have hsigma : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  unfold Ch03.poincareLowerEllipticityFactor
  have hlambda : 0 ≤ Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 4)
      (.finite 1) (aCutoffEnvelopeTriadicCoeffFamily M L omega) :=
    Ch02.lambdaSq_finite_nonneg _ _ (by norm_num) (by norm_num)
  have hnegRpow : Real.rpow
      (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)) (-(1 / 2 : ℝ)) =
      (Real.sqrt (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)))⁻¹ := by
    calc
      _ = (Real.rpow
          (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 4) (.finite 1)
            (aCutoffEnvelopeTriadicCoeffFamily M L omega)) (1 / 2 : ℝ))⁻¹ := by
        simpa only [Real.instPow] using! Real.rpow_neg hlambda (1 / 2 : ℝ)
      _ = _ := congrArg Inv.inv (by
        simpa only [Real.instPow] using!
          (Real.sqrt_eq_rpow (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 4)
            (.finite 1) (aCutoffEnvelopeTriadicCoeffFamily M L omega))).symm)
  rw [hnegRpow, mul_pow, inv_pow,
    Real.sq_sqrt hlambda]
  field_simp

/-- Upper squared Poincare factor: integrability and its explicit second-
moment budget after restoring the deterministic normalization. -/
theorem integrable_sq_and_integral_sq_oneStepUpperPoincareEnergyFactor_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (herror : paperENNRealLpNorm M.P.toMeasure 4
        (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) ≤
      ENNReal.ofReal R) :
    let D := Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) ^ 2 *
      ahom M L
    Integrable (fun omega ↦
      oneStepUpperPoincareEnergyFactorMeasurable M L m omega ^ 2)
        M.P.toMeasure ∧
      ∫ omega, oneStepUpperPoincareEnergyFactorMeasurable M L m omega ^ 2
          ∂M.P.toMeasure ≤
        (D * (1 + Real.sqrt 2 * R) ^ 2) ^ 2 := by
  dsimp only
  obtain ⟨hint, hbudget⟩ :=
    integrable_sq_and_integral_sq_oneStepUpperEllipticityRatioMeasurable_le
      M L m hR herror
  let D : ℝ := Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) ^ 2 *
    ahom M L
  have heq : (fun omega ↦
      oneStepUpperPoincareEnergyFactorMeasurable M L m omega ^ 2) =
      fun omega ↦ D ^ 2 *
        oneStepUpperEllipticityRatioMeasurable M L m omega ^ 2 := by
    funext omega
    simp only [oneStepUpperPoincareEnergyFactorMeasurable, D]
    ring
  rw [heq]
  constructor
  · exact hint.const_mul _
  · rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hbudget (sq_nonneg D)).trans_eq (by ring)

/-- Lower squared Poincare factor, in the reciprocal normalization. -/
theorem integrable_sq_and_integral_sq_oneStepLowerPoincareEnergyFactor_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (herror : paperENNRealLpNorm M.P.toMeasure 4
        (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) ≤
      ENNReal.ofReal R) :
    let D := Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) ^ 2 *
      (ahom M L)⁻¹
    Integrable (fun omega ↦
      oneStepLowerPoincareEnergyFactorMeasurable M L m omega ^ 2)
        M.P.toMeasure ∧
      ∫ omega, oneStepLowerPoincareEnergyFactorMeasurable M L m omega ^ 2
          ∂M.P.toMeasure ≤
        (D * (1 + Real.sqrt 2 * R) ^ 2) ^ 2 := by
  dsimp only
  obtain ⟨hint, hbudget⟩ :=
    integrable_sq_and_integral_sq_oneStepLowerInvEllipticityRatioMeasurable_le
      M L m hR herror
  let D : ℝ := Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) ^ 2 *
    (ahom M L)⁻¹
  have heq : (fun omega ↦
      oneStepLowerPoincareEnergyFactorMeasurable M L m omega ^ 2) =
      fun omega ↦ D ^ 2 *
        oneStepLowerInvEllipticityRatioMeasurable M L m omega ^ 2 := by
    funext omega
    simp only [oneStepLowerPoincareEnergyFactorMeasurable, D]
    ring
  rw [heq]
  constructor
  · exact hint.const_mul _
  · rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hbudget (sq_nonneg D)).trans_eq (by ring)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
