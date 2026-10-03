module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.BadEventLane
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.TranslatedDefect
public import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.OneCubeEllipticityComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.EllipticityErrorAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Bounds
public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem measurable_paperScalarProbeMax_cutoff_translate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    (R : TriadicCube d) :
    Measurable (fun omega : Sample d =>
      paperScalarProbeMax R
        (aCutoffFamily M L (translatePotentialSequence z omega)) (ahom M L)) := by
  change Measurable (fun omega : Sample d =>
    normalizedDefect M L (Ch02.cubeDomain R)
      (translatePotentialSequence z omega))
  exact ((measurable_normalizedDefect_potentialShellIndexSigma_Iic M L
    (Ch02.cubeDomain R)).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl).comp
        (measurable_translatePotentialSequence z)

/-- The literal pointwise `q = 1` paper homogenization-error random variable
is measurable.  No measurable modification is introduced: the proof expands
the countable depth sum, descendant supremum, and unit-sphere response maximum
through the already measurable normalized-defect carrier. -/
theorem measurable_translatedHomogenizationErrorRandom_one {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ)
    (z : PaperCubeTranslate d) {s : ℝ} :
    Measurable (translatedHomogenizationErrorRandom M L K z s 1) := by
  unfold translatedHomogenizationErrorRandom paperHomogenizationError
    paperHomogenizationErrorFinite paperScaleResponseAtScale
    paperMaxDescendantProbeAtScale
  apply ENNReal.continuous_rpow_const.measurable.comp
  apply Measurable.ennreal_tsum
  intro l
  apply measurable_const.mul
  apply ENNReal.continuous_rpow_const.measurable.comp
  apply ENNReal.continuous_rpow_const.measurable.comp
  exact Measurable.iSup fun R =>
    measurable_paperScalarProbeMax_cutoff_translate M L z R

/-- The exact measurability input requested by Step 7. -/
theorem measurable_translatedHomogenizationErrorRandom_quarter_one {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    Measurable (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) :=
  measurable_translatedHomogenizationErrorRandom_one M L m 0

/-! ## Deterministic bad-event assembly -/

/-- Numerical core of `e.bound.Lambdas.by.Es` at the threshold used in the
combine argument.  This formulation deliberately separates the analytic
comparison from the event bookkeeping: once both normalized ellipticity
ratios obey the printed comparison, an error below `1/5` forces the three
clauses of the good event. -/
private theorem ellipticity_clauses_of_error_lt_one_fifth
    {sigma lower upper error : ℝ} (hsigma : 0 < sigma) (hlower : 0 < lower)
    (hlowerUpper : lower ≤ upper)
    (hbound : max (sigma⁻¹ * upper) (sigma * lower⁻¹) ≤
      1 + 2 * error ^ 2 + 2 * error)
    (herror0 : 0 ≤ error) (herror : error < 1 / 5) :
    sigma / 2 ≤ lower ∧ lower ≤ upper ∧ upper ≤ 2 * sigma := by
  have hrhs : 1 + 2 * error ^ 2 + 2 * error < 2 := by
    nlinarith [sq_nonneg (error - 1 / 5)]
  have hupperRatio : sigma⁻¹ * upper < 2 :=
    (le_max_left _ _).trans_lt (hbound.trans_lt hrhs)
  have hlowerRatio : sigma * lower⁻¹ < 2 :=
    (le_max_right _ _).trans_lt (hbound.trans_lt hrhs)
  have hupper : upper ≤ 2 * sigma := by
    have := (inv_mul_lt_iff₀ hsigma).mp hupperRatio
    linarith
  have hlower' : sigma / 2 ≤ lower := by
    have htwo : (0 : ℝ) < 2 := by norm_num
    have hmul : sigma < 2 * lower := by
      have h := (mul_inv_lt_iff₀ hlower).mp hlowerRatio
      simpa [mul_comm] using h
    nlinarith
  exact ⟨hlower', hlowerUpper, hupper⟩

/-- Event-level form of the deterministic `e.bound.Lambdas.by.Es` assembly.
The three hypotheses preceding `hbound` are the literal positivity/order
facts for the ellipticity observables.  Keeping them explicit makes this
theorem valid for the measurable representatives used by
`coarseEllipticityGoodEvent`; they hold almost surely after rewriting those
representatives to the literal Chapter 4 observables. -/
theorem error_ge_one_fifth_of_not_mem_coarseEllipticityGoodEvent_of_bound
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (omega : Sample d)
    (hlower : 0 < cutoffLowerEllipticityMeasurable M L m omega)
    (hlowerUpper : cutoffLowerEllipticityMeasurable M L m omega ≤
      cutoffUpperEllipticityMeasurable M L m omega)
    (hbound : max
        ((ahom M L)⁻¹ * cutoffUpperEllipticityMeasurable M L m omega)
        (ahom M L * (cutoffLowerEllipticityMeasurable M L m omega)⁻¹) ≤
      1 + 2 *
          (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega).toReal ^ 2 +
        2 * (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega).toReal)
    (hbad : omega ∉ coarseEllipticityGoodEvent M L m) :
    (1 / 5 : ℝ≥0∞) ≤
      translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega := by
  by_contra hnot
  have herror : translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega <
      (1 / 5 : ℝ≥0∞) := lt_of_not_ge hnot
  have herrorReal :
      (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega).toReal <
        1 / 5 := by
    have herror' :
        translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega <
          ENNReal.ofReal (1 / 5 : ℝ) := by
      simpa using herror
    rw [← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 5)]
    exact ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top herror'
  have hsigma : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hgood := ellipticity_clauses_of_error_lt_one_fifth hsigma hlower
    hlowerUpper hbound ENNReal.toReal_nonneg herrorReal
  exact hbad hgood

/-! ## Literal cutoff comparison and the measurable-version boundary -/

/-- Pointwise analytic content of `e.bound.Lambdas.by.Es` for the GMC cutoff.
If the literal paper error is below `1/5`, the literal Chapter 4 upper and
lower multiscale ellipticities satisfy all three printed good-event clauses. -/
theorem literal_cutoff_ellipticity_clauses_of_error_lt_one_fifth
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) (omega : Sample d)
    (herror : translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega <
      (1 / 5 : ℝ≥0∞)) :
    ahom M L / 2 ≤
        Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) ∧
      Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) ≤
        Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) ∧
      Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) ≤ 2 * ahom M L := by
  let Q : TriadicCube d := originCube d (m : ℤ)
  let F := aCutoffEnvelopeTriadicCoeffFamily M L omega
  let hlocal := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega
  have hAEEq :
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (aCutoffRegCoeffField M L omega) hlocal).AEEq F := by
    simpa [F, hlocal] using aCutoff_canonicalFamily_aeeq M L omega
  have hupperEq :
      Ch04.LambdaSqCoeffField Q (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) =
        Ch02.LambdaSq Q (1 / 4) (.finite 1) F := by
    unfold Ch04.LambdaSqCoeffField
    rw [dif_pos hlocal]
    exact Ch02.LambdaSq_eq_ofAEEq hAEEq Q (1 / 4) (.finite 1)
  have hlowerEq :
      Ch04.lambdaSqCoeffField Q (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) =
        Ch02.lambdaSq Q (1 / 4) (.finite 1) F := by
    unfold Ch04.lambdaSqCoeffField
    rw [dif_pos hlocal]
    exact Ch02.lambdaSq_eq_ofAEEq hAEEq Q (1 / 4) (.finite 1)
  have hF : ∀ R, (F.coeffOn R).IsSymmetric := by
    intro R
    exact (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube R
      |>.isSymmetric
  have hsigma : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  have htranslate : translatePotentialSample (0 : Vec d) omega = omega := by
    funext k
    apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
    intro x
    change omega k (x + 0) = omega k x
    rw [add_zero]
  have hpaperEq :
      translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega =
        paperHomogenizationError Q (m : ℤ) (1 / 4) .infinity (.finite 1) F
          (ahom M L) := by
    unfold translatedHomogenizationErrorRandom
    rw [htranslate]
    simpa [Q, F, aCutoffFamily] using!
      (paperHomogenizationError_toTriadicCoeffFamily_eq
        (aCutoffTriadicData M L omega)
        (aCutoffEnvelopeScalarTriadicCoeffData M L omega)
        Q (m : ℤ) (1 / 4) .infinity (.finite 1) (ahom M L))
  have hcomparison :=
    ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
      Q F hF (by norm_num : (0 : ℝ) < 1 / 4) hsigma
  have herrorF :
      paperHomogenizationError Q Q.scale (1 / 4) .infinity (.finite 1) F
          (ahom M L) < (1 / 5 : ℝ≥0∞) := by
    rw [show Q.scale = (m : ℤ) by simp [Q, originCube]]
    rw [← hpaperEq]
    exact herror
  have hrealError :
      Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 1) F
          (scalarMatrix (d := d) (ahom M L)) < 1 / 5 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 5)).mp
    exact hcomparison.trans_lt (by simpa using herrorF)
  have hmax := ErrorComparison.max_weightedEllipticity_lt_two_of_error_lt_one_fifth
    Q F (by norm_num : (0 : ℝ) < 1 / 4) hsigma hrealError
  have hlowerPos : 0 < Ch02.lambdaSq Q (1 / 4) (.finite 1) F :=
    Ch02.lambdaSq_finite_pos Q F (by norm_num) (by norm_num)
  have hlowerUpper : Ch02.lambdaSq Q (1 / 4) (.finite 1) F ≤
      Ch02.LambdaSq Q (1 / 4) (.finite 1) F :=
    (Ch02.lambdaSq_le_oneCube Q F (by norm_num) (by norm_num)).trans
      ((Ch02.oneCube_sigmaStarInv_le_b Q F).trans
        (Ch02.oneCube_b_le_LambdaSq Q F (by norm_num) (by norm_num)))
  have hupperRatio : (ahom M L)⁻¹ *
      Ch02.LambdaSq Q (1 / 4) (.finite 1) F < 2 :=
    (le_max_left _ _).trans_lt hmax
  have hlowerRatio : ahom M L *
      (Ch02.lambdaSq Q (1 / 4) (.finite 1) F)⁻¹ < 2 :=
    (le_max_right _ _).trans_lt hmax
  have hupper : Ch02.LambdaSq Q (1 / 4) (.finite 1) F ≤ 2 * ahom M L := by
    have := (inv_mul_lt_iff₀ hsigma).mp hupperRatio
    linarith
  have hlower : ahom M L / 2 ≤ Ch02.lambdaSq Q (1 / 4) (.finite 1) F := by
    have hmul := (mul_inv_lt_iff₀ hlowerPos).mp hlowerRatio
    nlinarith
  change ahom M L / 2 ≤
      Ch04.lambdaSqCoeffField Q (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) ∧
    Ch04.lambdaSqCoeffField Q (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) ≤
      Ch04.LambdaSqCoeffField Q (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) ∧
    Ch04.LambdaSqCoeffField Q (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega) ≤ 2 * ahom M L
  rw [hupperEq, hlowerEq]
  exact ⟨hlower, hlowerUpper, hupper⟩

/-- Deterministic event-inclusion form of the preceding literal-cutoff
comparison. -/
theorem literal_coarseEllipticity_compl_subset_error_threshold
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    {omega : Sample d |
        ahom M L / 2 ≤
            Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
              (aCutoffRegCoeffField M L omega) ∧
          Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
              (aCutoffRegCoeffField M L omega) ≤
            Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
              (aCutoffRegCoeffField M L omega) ∧
          Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
              (aCutoffRegCoeffField M L omega) ≤ 2 * ahom M L}ᶜ ⊆
      {omega | (1 / 5 : ℝ≥0∞) ≤
        translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega} := by
  intro omega hbad
  by_contra hnot
  exact hbad (literal_cutoff_ellipticity_clauses_of_error_lt_one_fifth
    M L m omega (lt_of_not_ge hnot))

/-- The strongest event comparison justified by the current measurable-version
API: the requested complement inclusion holds almost surely.  A literal set
inclusion would require pointwise, rather than a.e., identification of the two
`AEMeasurable.mk` representatives in `ResponseMeasureTheory`. -/
theorem ae_error_ge_one_fifth_of_not_mem_coarseEllipticityGoodEvent
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      omega ∉ coarseEllipticityGoodEvent M L m →
        (1 / 5 : ℝ≥0∞) ≤
          translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega := by
  filter_upwards [cutoffLowerEllipticityMeasurable_ae_eq M L m,
    cutoffUpperEllipticityMeasurable_ae_eq M L m] with omega hlowerEq hupperEq
  intro hbad
  by_contra hnot
  have herror : translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega <
      (1 / 5 : ℝ≥0∞) := lt_of_not_ge hnot
  have hliteral := literal_cutoff_ellipticity_clauses_of_error_lt_one_fifth
    M L m omega herror
  have hgood : omega ∈ coarseEllipticityGoodEvent M L m := by
    simpa [coarseEllipticityGoodEvent, hlowerEq, hupperEq] using hliteral
  exact hbad hgood

/-! ## Concrete Step-7 probability bound -/

/-- Complete bad-event instantiation for the measurable coarse-ellipticity
event.  The sole proof-layer premise is the exact conclusion shape of the
still-draft large-cube response theorem; measurability and the threshold
comparison are discharged internally. -/
theorem coarseEllipticityBadEvent_probability_le_of_multiscaleResponseLargeCubes
    {d : ℕ} (hLarge : MultiscaleResponseLargeCubesConclusion d) :
    ∃ c CB : ℝ, 0 < c ∧ 0 < CB ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m0 m : ℕ)
        (delta1 xi : ℝ),
        M.delta ^ 2 ≤ delta1 → delta1 < 1 → L ≤ m0 → L ≤ m →
        16 * (d : ℝ) ≤ xi →
        xi ≤ c * (1 / 4 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 xi delta1 →
        M.P.toMeasure.real (coarseEllipticityGoodEvent M L m)ᶜ ≤
          Real.rpow (CB * delta1) (xi / 2) := by
  rcases badEvent_probability_le_of_multiscaleResponseLargeCubes hLarge with
    ⟨c, CB, hc, hCB, htailBound⟩
  refine ⟨c, CB, hc, hCB, ?_⟩
  intro M L m0 m delta1 xi hdelta hdelta1 hLm0 hLm hxi hxic hS
  letI : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  let T : Set (Sample d) :=
    {omega | ENNReal.ofReal (1 / 5 : ℝ) ≤
      translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega}
  have htail : M.P.toMeasure.real T ≤
      Real.rpow (CB * delta1) (xi / 2) :=
    htailBound M L m0 m delta1 xi hdelta hdelta1 hLm0 hLm hxi hxic hS T
      (measurable_translatedHomogenizationErrorRandom_quarter_one M L m)
      (by intro omega homega; exact homega)
  have hae : (coarseEllipticityGoodEvent M L m)ᶜ ≤ᵐ[M.P.toMeasure] T := by
    filter_upwards
      [ae_error_ge_one_fifth_of_not_mem_coarseEllipticityGoodEvent M L m]
      with omega homega
    intro hbad
    change ENNReal.ofReal (1 / 5 : ℝ) ≤
      translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega
    simpa using homega hbad
  have hmeasure : M.P.toMeasure (coarseEllipticityGoodEvent M L m)ᶜ ≤
      M.P.toMeasure T := measure_mono_ae hae
  calc
    M.P.toMeasure.real (coarseEllipticityGoodEvent M L m)ᶜ ≤
        M.P.toMeasure.real T := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top M.P.toMeasure T) hmeasure
    _ ≤ Real.rpow (CB * delta1) (xi / 2) := htail

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
