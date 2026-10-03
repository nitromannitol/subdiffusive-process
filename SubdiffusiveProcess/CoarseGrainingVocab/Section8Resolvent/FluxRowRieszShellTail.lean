module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszShellSummation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Quantitative stochastic input for the graph-shell factor.  In the paper,
the moment field is produced by the large-cube multiscale moments, the
large-cube ellipticity moments, the maximal inequality over eligible cubes,
and the source-cell tail. -/
structure FluxRowRieszShellMomentInput
    (mu : Measure Omega) (beta : ℝ) (shell : ℕ → Omega → ℝ)
    (p : ℕ) (K C A : ℝ) : Prop where
  beta_nonneg : 0 ≤ beta
  shell_nonneg : ∀ j omega, 0 ≤ shell j omega
  factor_measurable : Measurable (wholeSpaceFluxPartitionFactor beta shell)
  moment_order_pos : 0 < p
  moment_bound_one : 1 ≤ K
  log_moment_bound_le : Real.log K ≤ C
  reciprocal_order_le_scale : (p : ℝ)⁻¹ ≤ A
  factor_pow_integrable : Integrable
    (fun omega ↦ wholeSpaceFluxPartitionFactor beta shell omega ^ p) mu
  factor_moment_le :
    ∫ omega, wholeSpaceFluxPartitionFactor beta shell omega ^ p ∂mu ≤ K ^ p

/-- The quantitative shell input gives the lower bound and logarithmic
`O_{Gamma_1}` tail of the exact random partition factor. -/
theorem FluxRowRieszShellMomentInput.one_le_and_ogammaLE
    [IsProbabilityMeasure mu]
    {beta : ℝ} {shell : ℕ → Omega → ℝ} {p : ℕ} {K C A : ℝ}
    (H : FluxRowRieszShellMomentInput mu beta shell p K C A) :
    (∀ omega, 1 ≤ wholeSpaceFluxPartitionFactor beta shell omega) ∧
      SubdiffusiveProcess.OGammaLE mu 1 A
        (fun omega ↦
          Real.log (wholeSpaceFluxPartitionFactor beta shell omega) - C) := by
  exact wholeSpaceFluxPartitionFactor_one_le_and_ogammaLE_of_nat_moment
    H.beta_nonneg H.shell_nonneg H.factor_measurable H.moment_order_pos
    H.moment_bound_one H.log_moment_bound_le H.reciprocal_order_le_scale
    H.factor_pow_integrable H.factor_moment_le

/-- Probability-facing endpoint of item 4.  A price bound using the exact
shell factor and its quantitative moment input simultaneously provides the
whole-space cell-price estimate and the required logarithmic tail for `Z`. -/
theorem fluxRowRieszCellPriceSum_and_ogammaLE_of_shellMoment
    [IsProbabilityMeasure mu]
    {beta : ℝ} {shell : ℕ → Omega → ℝ} {p : ℕ} {K C A : ℝ}
    (H : FluxRowRieszShellMomentInput mu beta shell p K C A)
    {omega : Omega} {priceSum CSigma physicalScale : ℝ}
    (hprice : priceSum ≤
      CSigma * wholeSpaceFluxPartitionFactor beta shell omega * physicalScale) :
    priceSum ≤
        CSigma * wholeSpaceFluxPartitionFactor beta shell omega * physicalScale ∧
      (∀ omega, 1 ≤ wholeSpaceFluxPartitionFactor beta shell omega) ∧
      SubdiffusiveProcess.OGammaLE mu 1 A
        (fun omega ↦
          Real.log (wholeSpaceFluxPartitionFactor beta shell omega) - C) := by
  exact ⟨hprice, H.one_le_and_ogammaLE.1, H.one_le_and_ogammaLE.2⟩

omit [MeasurableSpace Omega] in
/-- For nonnegative summable shells the weighted sum is the real part of an
extended-nonnegative series, the form in which it is measurable. -/
theorem wholeSpaceFluxWeightedSum_eq_toReal_ennreal_tsum
    {beta : ℝ} (hbeta : 0 ≤ beta) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (hsummable : ∀ omega, Summable fun j ↦ beta ^ j * shell j omega)
    (omega : Omega) :
    wholeSpaceFluxWeightedSum beta shell omega =
      (∑' j : ℕ, ENNReal.ofReal (beta ^ j * shell j omega)).toReal := by
  unfold wholeSpaceFluxWeightedSum
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (pow_nonneg hbeta j) (hshell j omega)) (hsummable omega),
    ENNReal.toReal_ofReal (tsum_nonneg fun j => mul_nonneg (pow_nonneg hbeta j) (hshell j omega))]

/-- **Measurability of the random partition factor** from a measurable,
nonnegative, summable shell field. -/
theorem measurable_wholeSpaceFluxPartitionFactor
    {beta : ℝ} (hbeta : 0 ≤ beta) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (hsummable : ∀ omega, Summable fun j ↦ beta ^ j * shell j omega)
    (hmeas : ∀ j, Measurable (shell j)) :
    Measurable (wholeSpaceFluxPartitionFactor beta shell) := by
  have h : ∀ omega, wholeSpaceFluxWeightedSum beta shell omega =
      (∑' j : ℕ, ENNReal.ofReal (beta ^ j * shell j omega)).toReal := fun omega ↦
    wholeSpaceFluxWeightedSum_eq_toReal_ennreal_tsum hbeta hshell hsummable omega
  unfold wholeSpaceFluxPartitionFactor
  simp only [h]
  exact measurable_const.add
    ((Measurable.ennreal_tsum fun j ↦
      ENNReal.measurable_ofReal.comp (measurable_const.mul (hmeas j))).ennreal_toReal)

/-- The stochastic shell input assembled from a measurable shell field, its
summability, and the moment bound. -/
theorem fluxRowRieszShellMomentInput_of_measurable_shell
    {mu : Measure Omega} {beta : ℝ} {shell : ℕ → Omega → ℝ} {p : ℕ} {K C A : ℝ}
    (hbeta : 0 ≤ beta) (hshell : ∀ j omega, 0 ≤ shell j omega)
    (hsummable : ∀ omega, Summable fun j ↦ beta ^ j * shell j omega)
    (hmeas : ∀ j, Measurable (shell j))
    (hp : 0 < p) (hK : 1 ≤ K) (hlogK : Real.log K ≤ C) (hA : (p : ℝ)⁻¹ ≤ A)
    (hintegrable : Integrable
      (fun omega ↦ wholeSpaceFluxPartitionFactor beta shell omega ^ p) mu)
    (hmoment : ∫ omega, wholeSpaceFluxPartitionFactor beta shell omega ^ p ∂mu
      ≤ K ^ p) :
    FluxRowRieszShellMomentInput mu beta shell p K C A := by
  exact
    { beta_nonneg := hbeta
      shell_nonneg := hshell
      factor_measurable :=
        measurable_wholeSpaceFluxPartitionFactor hbeta hshell hsummable hmeas
      moment_order_pos := hp
      moment_bound_one := hK
      log_moment_bound_le := hlogK
      reciprocal_order_le_scale := hA
      factor_pow_integrable := hintegrable
      factor_moment_le := hmoment }

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
