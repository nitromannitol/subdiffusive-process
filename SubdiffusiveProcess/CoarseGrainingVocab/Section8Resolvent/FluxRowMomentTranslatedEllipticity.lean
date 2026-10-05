module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentTranslatedError
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepEllipticityFactorMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceCellEllipticityCovariance

@[expose] public section

/-!
# Translated high-order lower-ellipticity moments for the flux row

The flux-cell weight contains the factor
`ahom L * lambda_{1/16,1}^{-1}` on a deterministic translated cube.  This
module constructs a measurable representative of that factor, proves its
translation law, and bounds every admissible moment through the translated
large-cube homogenization error.  The exponent cost is explicit: an
`L^p`-bound for the factor uses the `L^(2p)` bound for the square-root error
comparison.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

theorem aemeasurable_fluxRowMoment_lowerInv_literal
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    AEMeasurable (fun omega : Sample d =>
      (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 16) (.finite 1)
        (aCutoffRegCoeffField M L omega))⁻¹) M.P.toMeasure := by
  have h := (aCutoffRestrictionLaw_lawCarrier M L)
    |>.aemeasurable_lambdaSqCoeffField_finite_one_inv
      (originCube d (m : ℤ)) (by norm_num : (0 : ℝ) < 1 / 16)
  simpa [aCutoffRestrictionLaw_eq_map, Function.comp_def] using
    h.comp_aemeasurable (measurable_aCutoffRegCoeffField M L).aemeasurable

/-- A nonnegative measurable representative of
`lambda_{1/16,1}^{-1}` on the centered scale-`m` cube. -/
noncomputable def fluxRowMomentLowerInvMeasurable {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) : Sample d → ℝ :=
  fun omega => max 0 <|
    AEMeasurable.mk
      (fun omega : Sample d =>
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 16) (.finite 1)
          (aCutoffRegCoeffField M L omega))⁻¹)
      (aemeasurable_fluxRowMoment_lowerInv_literal M L m) omega

theorem measurable_fluxRowMomentLowerInvMeasurable
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    Measurable (fluxRowMomentLowerInvMeasurable M L m) := by
  exact measurable_const.max
    (aemeasurable_fluxRowMoment_lowerInv_literal M L m).measurable_mk

theorem fluxRowMomentLowerInvMeasurable_nonneg
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (omega : Sample d) :
    0 ≤ fluxRowMomentLowerInvMeasurable M L m omega :=
  le_max_left _ _

theorem fluxRowMomentLowerInvMeasurable_ae_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    fluxRowMomentLowerInvMeasurable M L m =ᵐ[M.P.toMeasure]
      fun omega =>
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 16) (.finite 1)
          (aCutoffRegCoeffField M L omega))⁻¹ := by
  filter_upwards
      [(aemeasurable_fluxRowMoment_lowerInv_literal M L m).ae_eq_mk.symm]
      with omega heq
  rw [fluxRowMomentLowerInvMeasurable, heq, max_eq_right]
  exact inv_nonneg.mpr
    (Ch04.lambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num))

/-- The measurable lower-ellipticity inverse at an arbitrary deterministic
translate. -/
noncomputable def fluxRowMomentTranslatedLowerInv {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (z : PaperCubeTranslate d) : Sample d → ℝ :=
  fun omega => fluxRowMomentLowerInvMeasurable M L m
    (translatePotentialSample z omega)

theorem measurable_fluxRowMomentTranslatedLowerInv
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (z : PaperCubeTranslate d) :
    Measurable (fluxRowMomentTranslatedLowerInv M L m z) :=
  (measurable_fluxRowMomentLowerInvMeasurable M L m).comp
    (measurable_translatePotentialSequence z)

theorem fluxRowMomentTranslatedLowerInv_nonneg
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (z : PaperCubeTranslate d) (omega : Sample d) :
    0 ≤ fluxRowMomentTranslatedLowerInv M L m z omega :=
  fluxRowMomentLowerInvMeasurable_nonneg M L m _

private theorem fluxRowMoment_cutoff_family_lambdaSq_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 16) (.finite 1)
        (aCutoffRegCoeffField M L omega) =
      Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 16) (.finite 1)
        (aCutoffEnvelopeTriadicCoeffFamily M L omega) := by
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  unfold Ch04.lambdaSqCoeffField
  rw [dite_eq_left hlocal]
  exact Ch02.lambdaSq_eq_ofAEEq
    (by simpa using aCutoff_canonicalFamily_aeeq M L omega)
    (originCube d (m : ℤ)) (1 / 16) (.finite 1)

theorem aux_dedup_d098_fluxRowMoment_cutoff_paperError_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    translatedHomogenizationErrorRandom M L m 0 (1 / 16) 1 omega =
      paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) (1 / 16)
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
  simpa [aCutoffFamily] using!
    (paperHomogenizationError_toTriadicCoeffFamily_eq
      (aCutoffTriadicData M L omega)
      (aCutoffEnvelopeScalarTriadicCoeffData M L omega)
      (originCube d (m : ℤ)) (m : ℤ) (1 / 16) .infinity (.finite 1)
      (ahom M L))

private theorem fluxRowMoment_cutoff_paperError_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    translatedHomogenizationErrorRandom M L m 0 (1 / 16) 1 omega =
      paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) (1 / 16)
        .infinity (.finite 1) (aCutoffEnvelopeTriadicCoeffFamily M L omega)
          (ahom M L) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.aux_dedup_d098_fluxRowMoment_cutoff_paperError_eq (d := d) (M := M) (L := L) (m := m) (omega := omega)

private theorem ofReal_sqrt_fluxRowMoment_lowerInv_literal_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : Sample d) :
    ENNReal.ofReal (Real.sqrt (ahom M L *
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 16) (.finite 1)
          (aCutoffRegCoeffField M L omega))⁻¹)) ≤
      1 + ENNReal.ofReal (Real.sqrt 2) *
        translatedHomogenizationErrorRandom M L m 0 (1 / 16) 1 omega := by
  let Q := originCube d (m : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M L omega
  have hsigma : 0 < ahom M L := ahom_pos M L
  have hroot :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_mul_lambdaSq_inv_le_one_add_sqrt_two_mul_error
      Q F (by norm_num : (0 : ℝ) < 1 / 16) hsigma
  have hcompare :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
      Q F (fun R =>
        (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube R
          |>.isSymmetric)
      (by norm_num : (0 : ℝ) < 1 / 16) hsigma
  rw [fluxRowMoment_cutoff_family_lambdaSq_eq M L m omega]
  calc
    ENNReal.ofReal (Real.sqrt (ahom M L *
        (Ch02.lambdaSq Q (1 / 16) (.finite 1) F)⁻¹)) ≤
        ENNReal.ofReal (1 + Real.sqrt 2 *
          Ch02.HomogenizationErrorOnCube Q (1 / 16) .infinity (.finite 1) F
            (scalarMatrix (d := d) (ahom M L))) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q (1 / 16) .infinity (.finite 1) F
            (scalarMatrix (d := d) (ahom M L))) := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (mul_nonneg (Real.sqrt_nonneg 2)
            (Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q F _
              (by norm_num : (0 : ℝ) < 1 / 16))),
        ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
        paperHomogenizationError Q Q.scale (1 / 16) .infinity (.finite 1) F
          (ahom M L) := by gcongr
    _ = _ := by
      rw [show Q.scale = (m : ℤ) by simp [Q, originCube],
        ← fluxRowMoment_cutoff_paperError_eq M L m omega]

theorem aux_dedup_d111_translatedHomogenizationErrorRandom_zero_comp_translate
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (z : PaperCubeTranslate d) (s : ℝ) (r : ℕ) (omega : Sample d) :
    translatedHomogenizationErrorRandom M L m 0 s r
        (translatePotentialSample z omega) =
      translatedHomogenizationErrorRandom M L m z s r omega := by
  unfold translatedHomogenizationErrorRandom
  congr 2
  funext k
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  change omega k ((x + 0) + z) = omega k (x + z)
  rw [add_zero]

private theorem translatedHomogenizationErrorRandom_zero_comp_translate
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (z : PaperCubeTranslate d) (s : ℝ) (r : ℕ) (omega : Sample d) :
    translatedHomogenizationErrorRandom M L m 0 s r
        (translatePotentialSample z omega) =
      translatedHomogenizationErrorRandom M L m z s r omega := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.aux_dedup_d111_translatedHomogenizationErrorRandom_zero_comp_translate (d := d) (M := M) (L := L) (m := m) (z := z) (s := s) (r := r) (omega := omega)

private theorem fluxRowMomentTranslatedLowerInv_ae_eq_literal
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (z : PaperCubeTranslate d) :
    fluxRowMomentTranslatedLowerInv M L m z =ᵐ[M.P.toMeasure]
      fun omega =>
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 16) (.finite 1)
          (aCutoffRegCoeffField M L (translatePotentialSample z omega)))⁻¹ := by
  simpa only [fluxRowMomentTranslatedLowerInv, Function.comp_def] using!
    (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.measurePreserving_translatePotentialSequence
      M z).quasiMeasurePreserving
      |>.ae_eq_comp (fluxRowMomentLowerInvMeasurable_ae_eq M L m)

/-- The translated measurable inverse obeys the literal square-root error
comparison almost surely. -/
theorem ae_ofReal_sqrt_ahom_mul_fluxRowMomentTranslatedLowerInv_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (z : PaperCubeTranslate d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ENNReal.ofReal (Real.sqrt
          (ahom M L * fluxRowMomentTranslatedLowerInv M L m z omega)) ≤
        1 + ENNReal.ofReal (Real.sqrt 2) *
          translatedHomogenizationErrorRandom M L m z (1 / 16) 1 omega := by
  filter_upwards [fluxRowMomentTranslatedLowerInv_ae_eq_literal M L m z]
    with omega heq
  rw [heq, ← translatedHomogenizationErrorRandom_zero_comp_translate]
  exact ofReal_sqrt_fluxRowMoment_lowerInv_literal_le
    M L m (translatePotentialSample z omega)

/-- A `p`-moment of the translated ellipticity factor is controlled by the
`2p`-moment of the translated `q = 1` homogenization error. -/
theorem paperENNRealLpNorm_ahom_mul_fluxRowMomentTranslatedLowerInv_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (z : PaperCubeTranslate d) {p : ℝ} (hp : 1 ≤ p) :
    paperENNRealLpNorm M.P.toMeasure p (fun omega =>
        ENNReal.ofReal
          (ahom M L * fluxRowMomentTranslatedLowerInv M L m z omega)) ≤
      (1 + ENNReal.ofReal (Real.sqrt 2) *
        paperENNRealLpNorm M.P.toMeasure (2 * p)
          (translatedHomogenizationErrorRandom M L m z (1 / 16) 1)) ^ 2 := by
  let X : Sample d → ℝ≥0∞ := fun omega =>
    ENNReal.ofReal (Real.sqrt
      (ahom M L * fluxRowMomentTranslatedLowerInv M L m z omega))
  have hXsq : (fun omega => ENNReal.ofReal
      (ahom M L * fluxRowMomentTranslatedLowerInv M L m z omega)) =
      fun omega => X omega ^ (2 : ℕ) := by
    funext omega
    dsimp only [X]
    have hnonneg : 0 ≤ ahom M L *
        fluxRowMomentTranslatedLowerInv M L m z omega :=
      mul_nonneg (ahom_pos M L).le
        (fluxRowMomentTranslatedLowerInv_nonneg M L m z omega)
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]
  rw [hXsq, SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_sq
    M.P.toMeasure (zero_lt_one.trans_le hp)]
  apply pow_le_pow_left'
  have hmono := paperENNRealLpNorm_mono_ae M.P.toMeasure
    (by positivity : 0 ≤ 2 * p)
    (ae_ofReal_sqrt_ahom_mul_fluxRowMomentTranslatedLowerInv_le M L m z)
  have hadd := paperENNRealLpNorm_add_le M.P.toMeasure
    (by linarith : 1 ≤ 2 * p)
    (measurable_const : Measurable (fun _ : Sample d => (1 : ℝ≥0∞))).aemeasurable
    ((SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.measurable_translatedHomogenizationErrorRandom_one
      (s := (1 / 16 : ℝ)) M L m z).const_mul
        (ENNReal.ofReal (Real.sqrt 2))).aemeasurable
  refine hmono.trans (hadd.trans ?_)
  rw [paperENNRealLpNorm_one M.P.toMeasure,
    paperENNRealLpNorm_const_mul_eq M.P.toMeasure (by positivity : 0 < 2 * p)
      (ENNReal.ofReal (Real.sqrt 2))]
  · exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.measurable_translatedHomogenizationErrorRandom_one
      (s := (1 / 16 : ℝ)) M L m z

/-- **The exact translated high-order ellipticity input for a flux-cell
weight.**  At shell order `p`, the conclusion is the required `4p` moment;
the large-cube anchor is used at order `8p`, and the unchanged induction and
order-cap hypotheses are displayed literally. -/
theorem exists_fluxRowMoment_translatedLowerInv_four_mul_lpnorm_bound
    {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (L m0 : ℕ) (delta1 p : ℝ),
        M.delta ^ 2 ≤ delta1 → delta1 < 1 → L ≤ m0 → 1 ≤ p →
        4 * (d : ℝ) * (1 / 16 : ℝ)⁻¹ ≤ 8 * p →
        8 * p ≤ c * (1 / 16 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 (8 * p) delta1 →
        ∀ m : ℕ, L ≤ m → ∀ z : PaperCubeTranslate d,
          paperENNRealLpNorm M.P.toMeasure (4 * p) (fun omega =>
              ENNReal.ofReal
                (ahom M L * fluxRowMomentTranslatedLowerInv M L m z omega)) ≤
            (1 + ENNReal.ofReal (Real.sqrt 2) *
              ENNReal.ofReal
                (C * Real.rpow (1 / 16 : ℝ) (-1) * Real.sqrt delta1)) ^ 2 := by
  obtain ⟨c, C, hc, hC, hlarge⟩ :=
    _root_.SubdiffusiveProcess.Section4.multiscale_response_large_cubes (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M L m0 delta1 p hdelta hdeltaOne hLm0 hp hdim horder hIH m hLm z
  have herror := hlarge M L m0 (1 / 16) delta1 (8 * p)
    (by norm_num) (by norm_num) hdelta hdeltaOne hLm0 hdim horder hIH
    m hLm z 1 (Or.inl rfl)
  have herror' :
      paperENNRealLpNorm M.P.toMeasure (8 * p)
          (translatedHomogenizationErrorRandom M L m z (1 / 16) 1) ≤
        ENNReal.ofReal
          (C * Real.rpow (1 / 16 : ℝ) (-1) * Real.sqrt delta1) := by
    simpa only [Nat.cast_one, div_one] using herror
  have hfactor :=
    paperENNRealLpNorm_ahom_mul_fluxRowMomentTranslatedLowerInv_le
      M L m z (p := 4 * p) (by linarith)
  norm_num only [show (2 : ℝ) * (4 * p) = 8 * p by ring] at hfactor
  refine hfactor.trans (pow_le_pow_left' ?_ 2)
  calc
    1 + ENNReal.ofReal (Real.sqrt 2) *
          paperENNRealLpNorm M.P.toMeasure (8 * p)
            (translatedHomogenizationErrorRandom M L m z (1 / 16) 1) ≤
        1 + ENNReal.ofReal (Real.sqrt 2) *
          ENNReal.ofReal
            (C * Real.rpow (1 / 16 : ℝ) (-1) * Real.sqrt delta1) := by
      gcongr

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
