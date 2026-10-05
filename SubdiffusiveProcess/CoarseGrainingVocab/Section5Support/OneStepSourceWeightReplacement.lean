module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFinalSpecialization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLayerReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepExponentialRemainder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellDerivativeAggregation

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Oscillation-only envelope for the fresh shell block on a translated
triadic cell.  Unlike `smallCubeBlockEnvelope`, it omits the shell value at
the center because the replacement estimate only needs differences. -/
def oneStepSourceCellShellOscillationEnvelope {d : ℕ}
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  ∑ j ∈ Finset.Icc (n + 1) (n + h),
    translatedSmallShellEnvelope j R.scale (cubeCenter R) omega

theorem measurable_oneStepSourceCellShellOscillationEnvelope {d : ℕ}
    (n h : ℕ) (R : TriadicCube d) :
    Measurable (oneStepSourceCellShellOscillationEnvelope n h R) := by
  unfold oneStepSourceCellShellOscillationEnvelope
  exact Finset.measurable_sum _ fun j _ ↦
    measurable_translatedSmallShellEnvelope j R.scale (cubeCenter R)

theorem oneStepSourceCellShellOscillationEnvelope_nonneg {d : ℕ}
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ oneStepSourceCellShellOscillationEnvelope n h R omega := by
  unfold oneStepSourceCellShellOscillationEnvelope
  exact Finset.sum_nonneg fun j _ ↦
    translatedSmallShellEnvelope_nonneg j R.scale (cubeCenter R) omega

/-- Translation covariance of the literal cutoff-ratio supremum.  The
translated law sees the source cell as the origin cube at the same scale. -/
theorem cutoffRatioSup_cube_eq_originCube_translatePotentialSequence
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (numerator denominator : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffRatioSup M numerator denominator (Ch02.cubeDomain R) omega =
      cutoffRatioSup M numerator denominator
        (Ch02.cubeDomain (originCube d R.scale))
        (translatePotentialSequence (triadicCubeShift R) omega) := by
  unfold cutoffRatioSup
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ openCubeSet R at hx
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R,
      mem_translateSet_iff_sub_mem] at hx
    refine ⟨x - triadicCubeShift R, ?_, ?_⟩
    · simpa only [Ch02.cubeDomain_coe] using! hx
    · rw [aCutoff_translatePotentialSequence,
        aCutoff_translatePotentialSequence]
      congr 2 <;> abel
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + triadicCubeShift R, ?_, ?_⟩
    · change x + triadicCubeShift R ∈ openCubeSet R
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R,
        mem_translateSet_iff_sub_mem]
      change x ∈ openCubeSet (originCube d R.scale) at hx
      simpa only [add_sub_cancel_right] using! hx
    · rw [aCutoff_translatePotentialSequence,
        aCutoff_translatePotentialSequence]

/-- The translated oscillation envelope is exactly the parent derivative
gauge times the source-to-parent scale ratio. -/
theorem oneStepSourceCellShellOscillationEnvelope_eq_scale_mul_gauge
    {d : ℕ} (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    oneStepSourceCellShellOscillationEnvelope n h R omega =
      (3 : ℝ) ^ (R.scale - (n : ℤ)) *
        oneStepShellDerivativeGauge n h (cubeCenter R) omega := by
  unfold oneStepSourceCellShellOscillationEnvelope
    oneStepShellDerivativeGauge
  rw [show Finset.Icc (n + 1) (n + h) =
      Finset.Ico (n + 1) (n + h + 1) by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : n + h + 1 - (n + 1) = h := by omega
  rw [hlen, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold translatedSmallShellEnvelope
  rw [← mul_assoc]
  congr 1
  rw [show ((3 : ℝ) ^ (k + 1))⁻¹ =
      (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) by
    rw [zpow_neg, zpow_natCast]]
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring_nf

private theorem mem_openCubeSet_sub_cubeCenter {d : ℕ}
    (R : TriadicCube d) {x : Vec d} (hx : x ∈ openCubeSet R) :
    x - cubeCenter R ∈ openCubeSet (originCube d R.scale) := by
  have htranslate := openCubeSet_eq_translateSet_originCube_of_triadicCube R
  rw [htranslate, mem_translateSet_iff_sub_mem] at hx
  exact hx

/-- One-point fresh-shell oscillation from the cell center. -/
theorem abs_oneStepCenteredShellAt_sub_center_le_envelope
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hscale : R.scale ≤ (n : ℤ)) {x : Vec d} (hx : x ∈ openCubeSet R) :
    |oneStepCenteredShellAt M n h x omega -
        oneStepCenteredShellAt M n h (cubeCenter R) omega| ≤
      oneStepSourceCellShellOscillationEnvelope n h R omega := by
  have hindices : cutoffShellIndices (n + h) (n : ℤ) =
      Finset.Icc (n + 1) (n + h) := by
    unfold cutoffShellIndices
    ext j
    simp only [Finset.mem_Icc]
    omega
  have hxcenter := mem_openCubeSet_sub_cubeCenter R hx
  dsimp only [oneStepCenteredShellAt]
  rw [sub_sub_sub_cancel_right, cutoffShellSum, cutoffShellSum,
    ← Finset.sum_sub_distrib, hindices]
  calc
    |∑ j ∈ Finset.Icc (n + 1) (n + h),
        (omega j x - omega j (cubeCenter R))| ≤
        ∑ j ∈ Finset.Icc (n + 1) (n + h),
          |omega j x - omega j (cubeCenter R)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc (n + 1) (n + h),
        translatedSmallShellEnvelope j R.scale (cubeCenter R) omega := by
      apply Finset.sum_le_sum
      intro j hj
      apply abs_shell_sub_le_translatedSmallShellEnvelope
      · exact hscale.trans (by
          have hjLower := (Finset.mem_Icc.mp hj).1
          exact_mod_cast (le_trans (Nat.le_add_right n 1) hjLower))
      · exact hxcenter
    _ = oneStepSourceCellShellOscillationEnvelope n h R omega := rfl

/-- All-pairs centered-shell oscillation on one source cell. -/
theorem abs_oneStepCenteredShellAt_sub_le_two_envelope
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hscale : R.scale ≤ (n : ℤ)) {x y : Vec d}
    (hx : x ∈ openCubeSet R) (hy : y ∈ openCubeSet R) :
    |oneStepCenteredShellAt M n h y omega -
        oneStepCenteredShellAt M n h x omega| ≤
      2 * oneStepSourceCellShellOscillationEnvelope n h R omega := by
  let c := oneStepCenteredShellAt M n h (cubeCenter R) omega
  have hyc := abs_oneStepCenteredShellAt_sub_center_le_envelope
    M n h R omega hscale hy
  have hxc := abs_oneStepCenteredShellAt_sub_center_le_envelope
    M n h R omega hscale hx
  calc
    |oneStepCenteredShellAt M n h y omega -
        oneStepCenteredShellAt M n h x omega| =
        |(oneStepCenteredShellAt M n h y omega - c) -
          (oneStepCenteredShellAt M n h x omega - c)| := by
            congr 1
            ring_nf
    _ ≤ |oneStepCenteredShellAt M n h y omega - c| +
        |oneStepCenteredShellAt M n h x omega - c| := abs_sub _ _
    _ ≤ oneStepSourceCellShellOscillationEnvelope n h R omega +
        oneStepSourceCellShellOscillationEnvelope n h R omega :=
      add_le_add hyc hxc
    _ = 2 * oneStepSourceCellShellOscillationEnvelope n h R omega := by ring

/-- Exact source-cell scale gain for the oscillation envelope. -/
theorem oneStepSourceCell_scale_ratio_le_delta_sixteen
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n K : ℕ) (R : TriadicCube d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) :
    (3 : ℝ) ^ (R.scale - (n : ℤ)) ≤ M.delta ^ (16 : ℕ) := by
  have hscale := oneStepSourceCells_scale_eq hK hR
  have hadd := oneStepLocalizationScale_add_depth hsource
  have hexponent : R.scale - (n : ℤ) =
      -(oneStepLocalizationDepth M.delta : ℤ) := by
    rw [hscale]
    omega
  rw [hexponent]
  have hfactor :
      (3 : ℝ) ^ (-(oneStepLocalizationDepth M.delta : ℤ)) =
        (3 : ℝ) ^ (-(oneStepLocalizationDepth M.delta : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  rw [hfactor]
  exact rpow_three_neg_oneStepLocalizationDepth_le_delta_pow_sixteen
    M.shellPrefix.delta_pos
    (M.shellPrefix.delta_le_half.trans (by norm_num))

/-- Eighth probability norm of the source-cell shell oscillation.  The
sixteen geometric powers from localization multiply the one derivative
power supplied by `(g2)`. -/
theorem eLpNorm_oneStepSourceCellShellOscillationEnvelope_eight_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h K : ℕ) (R : TriadicCube d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h) :
    eLpNorm (oneStepSourceCellShellOscillationEnvelope n h R)
        8 M.P.toMeasure ≤
      ENNReal.ofReal (oneStepDerivativeGaugeConst * M.delta ^ (17 : ℕ)) := by
  let a : ℝ := (3 : ℝ) ^ (R.scale - (n : ℤ))
  have ha0 : 0 ≤ a := (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le
  have ha := oneStepSourceCell_scale_ratio_le_delta_sixteen
    M n K R hsource hK hR
  have hgauge := eLpNorm_oneStepDerivativeGauge_eight_le
    M n h (cubeCenter R) hh
  have hconst : oneStepDerivativeGaugeEightBound M =
      oneStepDerivativeGaugeConst * M.delta := by
    unfold oneStepDerivativeGaugeEightBound oneStepDerivativeGaugeConst
    ring_nf
  rw [hconst] at hgauge
  have heq : oneStepSourceCellShellOscillationEnvelope n h R =
      fun omega ↦ a * oneStepShellDerivativeGauge n h (cubeCenter R) omega := by
    funext omega
    exact oneStepSourceCellShellOscillationEnvelope_eq_scale_mul_gauge
      n h R omega
  rw [heq]
  have hnorm : eLpNorm (fun omega ↦
      a * oneStepShellDerivativeGauge n h (cubeCenter R) omega)
      8 M.P.toMeasure =
      ENNReal.ofReal a *
        eLpNorm (oneStepShellDerivativeGauge n h (cubeCenter R))
          8 M.P.toMeasure := by
    simpa only [smul_eq_mul, Real.enorm_eq_ofReal ha0] using!
      (eLpNorm_const_smul a
        (oneStepShellDerivativeGauge n h (cubeCenter R)) 8 M.P.toMeasure)
  rw [hnorm]
  calc
    ENNReal.ofReal a *
        eLpNorm (oneStepShellDerivativeGauge n h (cubeCenter R))
          8 M.P.toMeasure ≤
        ENNReal.ofReal (M.delta ^ (16 : ℕ)) *
          ENNReal.ofReal (oneStepDerivativeGaugeConst * M.delta) := by
      exact mul_le_mul (ENNReal.ofReal_le_ofReal ha) hgauge (zero_le) (zero_le)
    _ = ENNReal.ofReal (oneStepDerivativeGaugeConst * M.delta ^ (17 : ℕ)) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg M.shellPrefix.delta_pos.le 16)]
      congr 1
      ring_nf

/-- The G2 finite-field estimate gives one translated measurable majorant
for both source-cell weights.  The quantitative fourth-root bound is kept in
its pre-absorption form so downstream estimates can spend only the factors
they need. -/
theorem exists_oneStepSourceCellWeight_commonMajorant
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h) :
    ∃ W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      Measurable W ∧ (∀ omega, 0 ≤ W omega) ∧
      Integrable (fun omega ↦ W omega ^ (4 : ℝ)) M.P.toMeasure ∧
      (∫ omega, W omega ^ (4 : ℝ) ∂M.P.toMeasure) ^ (4 : ℝ)⁻¹ ≤
        finiteFieldMomentConst d * Real.sqrt 4 * M.delta * Real.sqrt (h : ℝ) *
          Real.exp (finiteFieldMomentExpConst d * 4 * M.delta ^ 2 *
            (h : ℝ)) ∧
      (∀ omega, oneStepUpperSourceCellWeight M n h R omega ≤ W omega + 1) ∧
      ∀ omega, oneStepLowerSourceCellWeight M n h R omega ≤ W omega + 1 := by
  let Q := originCube d R.scale
  obtain ⟨W0, hW0m, hW00, hW0int, hW0bound, hW0fwd, hW0inv⟩ :=
    aman_Linfty_moments_source_bound M (n + h) n R.scale
      (Nat.lt_add_of_pos_right hh) 4 (by norm_num)
  have hsubset : ((Ch02.cubeDomain Q : Ch02.Domain d) : Set (Vec d)) ⊆
      openCubeSet (originCube d R.scale) := by
    intro x hx
    simpa only [Q, Ch02.cubeDomain_coe] using! hx
  have hmaj0 := cutoffRatioSup_le_commonMajorant M
    (Nat.lt_add_of_pos_right hh) (Ch02.cubeDomain Q) hsubset
      hW00 hW0fwd hW0inv
  let z := triadicCubeShift R
  let W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ W0 (translatePotentialSequence z omega)
  have hWm : Measurable W :=
    hW0m.comp (measurable_translatePotentialSequence z)
  have hWnonneg : ∀ omega, 0 ≤ W omega := fun omega ↦ hW00 _
  have hWint : Integrable (fun omega ↦ W omega ^ (4 : ℝ))
      M.P.toMeasure := by
    simpa only [W, Function.comp_apply] using!
      (measurePreserving_translatePotentialSequence M z).integrable_comp_of_integrable
        hW0int
  have hWintegral :
      (∫ omega, W omega ^ (4 : ℝ) ∂M.P.toMeasure) =
        ∫ omega, W0 omega ^ (4 : ℝ) ∂M.P.toMeasure := by
    exact integral_comp_translatePotentialSequence_eq M z
      (fun omega ↦ W0 omega ^ (4 : ℝ)) hW0int.aestronglyMeasurable
  have hgap : n + h - n = h := Nat.add_sub_cancel_left n h
  have hscale : R.scale ≤ (n : ℤ) := by
    rw [oneStepSourceCells_scale_eq hK hR]
    exact_mod_cast Nat.sub_le n (oneStepLocalizationDepth M.delta)
  have hmax : max 0 ((R.scale : ℝ) - n) = 0 := by
    rw [max_eq_left]
    exact sub_nonpos.mpr (by exact_mod_cast hscale)
  have hbound :
      (∫ omega, W omega ^ (4 : ℝ) ∂M.P.toMeasure) ^ (4 : ℝ)⁻¹ ≤
        finiteFieldMomentConst d * Real.sqrt 4 * M.delta * Real.sqrt (h : ℝ) *
          Real.exp (finiteFieldMomentExpConst d * 4 * M.delta ^ 2 *
            (h : ℝ)) := by
    rw [hWintegral]
    simpa only [hgap, hmax, pow_two, zero_mul, add_zero] using! hW0bound
  refine ⟨W, hWm, hWnonneg, hWint, hbound, ?_, ?_⟩
  · intro omega
    unfold oneStepUpperSourceCellWeight
    rw [cutoffRatioSup_cube_eq_originCube_translatePotentialSequence
      M (n + h) n R omega]
    simpa only [Q, W, z] using! hmaj0.1 (translatePotentialSequence z omega)
  · intro omega
    unfold oneStepLowerSourceCellWeight
    rw [cutoffRatioSup_cube_eq_originCube_translatePotentialSequence
      M n (n + h) R omega]
    simpa only [Q, W, z] using! hmaj0.2 (translatePotentialSequence z omega)

/-- Dimension-only fourth-root bound for the common source-cell weight
majorant in the one-step range `h ≤ delta⁻¹`. -/
def oneStepSourceCellWeightFourthRootConst (d : ℕ) : ℝ :=
  2 * finiteFieldMomentConst d *
    Real.exp (2 * finiteFieldMomentExpConst d)

theorem oneStepSourceCellWeightFourthRootConst_pos
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < oneStepSourceCellWeightFourthRootConst d := by
  unfold oneStepSourceCellWeightFourthRootConst finiteFieldMomentConst
  have hfinite : 0 < finiteFieldConst d + Real.log 2 / 2 := by
    exact add_pos_of_pos_of_nonneg (finiteFieldConst_pos M) (by positivity)
  have hmoment : 0 < 2 * Homogenization.IndependentSums.gammaMomentConst 2 *
      Real.sqrt 2 * (finiteFieldConst d + Real.log 2 / 2) := by
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num)
          (Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num)))
        (Real.sqrt_pos.mpr (by norm_num)))
      hfinite
  exact mul_pos (mul_pos (by norm_num) hmoment) (Real.exp_pos _)

/-- Uniform version of `exists_oneStepSourceCellWeight_commonMajorant`.
All dependence on the model and on the block length has been absorbed into
the fixed dimension-only constant. -/
theorem exists_oneStepSourceCellWeight_uniform_commonMajorant
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ∃ W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      Measurable W ∧ (∀ omega, 0 ≤ W omega) ∧
      Integrable (fun omega ↦ W omega ^ (4 : ℝ)) M.P.toMeasure ∧
      (∫ omega, W omega ^ (4 : ℝ) ∂M.P.toMeasure) ^ (4 : ℝ)⁻¹ ≤
        oneStepSourceCellWeightFourthRootConst d ∧
      (∀ omega, oneStepUpperSourceCellWeight M n h R omega ≤ W omega + 1) ∧
      ∀ omega, oneStepLowerSourceCellWeight M n h R omega ≤ W omega + 1 := by
  obtain ⟨W, hWm, hW0, hWint, hWroot, hWupper, hWlower⟩ :=
    exists_oneStepSourceCellWeight_commonMajorant M n h R hK hR hh
  have hdelta0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaOne : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  have hdh : M.delta * (h : ℝ) ≤ 1 := by
    calc
      M.delta * (h : ℝ) ≤ M.delta * M.delta⁻¹ :=
        mul_le_mul_of_nonneg_left hblock hdelta0.le
      _ = 1 := mul_inv_cancel₀ hdelta0.ne'
  have hd2h : M.delta ^ 2 * (h : ℝ) ≤ 1 / 2 := by
    calc
      M.delta ^ 2 * (h : ℝ) = M.delta * (M.delta * (h : ℝ)) := by ring
      _ ≤ M.delta * 1 :=
        mul_le_mul_of_nonneg_left hdh hdelta0.le
      _ ≤ 1 / 2 := by simpa using M.shellPrefix.delta_le_half
  have hsqrt : 0 ≤ Real.sqrt (h : ℝ) := Real.sqrt_nonneg _
  have hh0 : 0 ≤ (h : ℝ) := by positivity
  have hdeltaSqrt : M.delta * Real.sqrt (h : ℝ) ≤ 1 := by
    have hsqrtSq : (Real.sqrt (h : ℝ)) ^ 2 = (h : ℝ) :=
      Real.sq_sqrt hh0
    have hsquare : (M.delta * Real.sqrt (h : ℝ)) ^ 2 ≤ 1 ^ 2 := by
      rw [mul_pow, hsqrtSq]
      nlinarith
    nlinarith [mul_nonneg hdelta0.le hsqrt]
  have hC0 : 0 ≤ finiteFieldMomentConst d := by
    unfold finiteFieldMomentConst
    exact mul_nonneg
        (mul_nonneg
        (mul_nonneg (by norm_num)
          (Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num)).le)
        (Real.sqrt_nonneg 2))
      (add_nonneg (finiteFieldConst_pos M).le (by positivity))
  have hCexp : 0 ≤ finiteFieldMomentExpConst d := by
    unfold finiteFieldMomentExpConst
    positivity
  have hexponent :
      finiteFieldMomentExpConst d * 4 * M.delta ^ 2 * (h : ℝ) ≤
        2 * finiteFieldMomentExpConst d := by
    have hmul := mul_le_mul_of_nonneg_left hd2h
      (mul_nonneg hCexp (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hbound :
      finiteFieldMomentConst d * Real.sqrt 4 * M.delta * Real.sqrt (h : ℝ) *
          Real.exp (finiteFieldMomentExpConst d * 4 * M.delta ^ 2 * (h : ℝ)) ≤
        oneStepSourceCellWeightFourthRootConst d := by
    have hsqrtFour : Real.sqrt 4 = 2 := by
      have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith [Real.sqrt_nonneg 4]
    rw [hsqrtFour]
    unfold oneStepSourceCellWeightFourthRootConst
    have hpref :
        finiteFieldMomentConst d * 2 *
            (M.delta * Real.sqrt (h : ℝ)) ≤
          finiteFieldMomentConst d * 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hdeltaSqrt (mul_nonneg hC0 (by norm_num))
    calc
      finiteFieldMomentConst d * 2 * M.delta * Real.sqrt (h : ℝ) *
          Real.exp (finiteFieldMomentExpConst d * 4 * M.delta ^ 2 * (h : ℝ)) =
          (finiteFieldMomentConst d * 2 *
            (M.delta * Real.sqrt (h : ℝ))) *
              Real.exp (finiteFieldMomentExpConst d * 4 * M.delta ^ 2 *
                (h : ℝ)) := by ring
      _ ≤ (finiteFieldMomentConst d * 2 * 1) *
          Real.exp (2 * finiteFieldMomentExpConst d) :=
        mul_le_mul hpref hexp (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hC0 (by norm_num)) zero_le_one)
      _ = 2 * finiteFieldMomentConst d *
          Real.exp (2 * finiteFieldMomentExpConst d) := by ring
  exact ⟨W, hWm, hW0, hWint, hWroot.trans hbound, hWupper, hWlower⟩

/-- Both literal source-cell weights have a uniform dimension-only `L⁴`
norm in the one-step range. -/
theorem eLpNorm_oneStepSourceCellWeights_four_le
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    eLpNorm (oneStepUpperSourceCellWeight M n h R) 4 M.P.toMeasure ≤
        ENNReal.ofReal (oneStepSourceCellWeightFourthRootConst d + 1) ∧
      eLpNorm (oneStepLowerSourceCellWeight M n h R) 4 M.P.toMeasure ≤
        ENNReal.ofReal (oneStepSourceCellWeightFourthRootConst d + 1) := by
  obtain ⟨W, hWm, hW0, hWint, hWroot, hWupper, hWlower⟩ :=
    exists_oneStepSourceCellWeight_uniform_commonMajorant
      M n h R hK hR hh hblock
  have hWnat : Integrable (fun omega ↦ W omega ^ (4 : ℕ)) M.P.toMeasure := by
    convert hWint using 1
    funext omega
    exact (Real.rpow_natCast (W omega) 4).symm
  have hWmem : MemLp W 4 M.P.toMeasure := by
    rw [← integrable_norm_rpow_iff hWm.aestronglyMeasurable
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
    norm_num only [ENNReal.toReal_ofNat]
    convert hWint using 1
    funext omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 omega)]
  have hWnorm : eLpNorm W 4 M.P.toMeasure ≤
      ENNReal.ofReal (oneStepSourceCellWeightFourthRootConst d) := by
    rw [hWmem.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
    norm_num only [ENNReal.toReal_ofNat]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
    have hinv : (4 : ℝ)⁻¹ = 1 / 4 := by norm_num
    rw [hinv] at hWroot
    exact ENNReal.ofReal_le_ofReal hWroot
  have hone : MemLp (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ (1 : ℝ)) 4 M.P.toMeasure :=
    memLp_const 1
  have hsum := eLpNorm_add_le (μ := M.P.toMeasure) (f := W) (g := fun _ => (1 : ℝ)) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have honeNorm : eLpNorm (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ (1 : ℝ)) 4 M.P.toMeasure = 1 := by
    rw [eLpNorm_const (1 : ℝ) (by norm_num) (NeZero.ne M.P.toMeasure)]
    simp
  have hsumBound : eLpNorm (fun omega ↦ W omega + 1) 4 M.P.toMeasure ≤
      ENNReal.ofReal (oneStepSourceCellWeightFourthRootConst d + 1) := by
    calc
      eLpNorm (fun omega ↦ W omega + 1) 4 M.P.toMeasure ≤
          eLpNorm W 4 M.P.toMeasure +
            eLpNorm (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ (1 : ℝ)) 4 M.P.toMeasure := hsum
      _ ≤ ENNReal.ofReal (oneStepSourceCellWeightFourthRootConst d) + 1 := by
        rw [honeNorm]
        exact add_le_add hWnorm le_rfl
      _ = ENNReal.ofReal (oneStepSourceCellWeightFourthRootConst d + 1) := by
        rw [ENNReal.ofReal_add (oneStepSourceCellWeightFourthRootConst_pos M).le]
        all_goals norm_num
  constructor
  · exact (eLpNorm_mono_ae ((measurable_cutoffRatioSup M (n + h) n (Ch02.cubeDomain R)).aestronglyMeasurable) (Filter.Eventually.of_forall fun omega ↦ by
      have hpos : 0 < oneStepUpperSourceCellWeight M n h R omega := by
        unfold oneStepUpperSourceCellWeight
        exact cutoffRatioSup_pos M (n + h) n (Ch02.cubeDomain R) omega
      change ‖oneStepUpperSourceCellWeight M n h R omega‖ ≤ ‖W omega + 1‖
      rw [Real.norm_eq_abs, abs_of_pos
        hpos,
        Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hW0 omega) zero_le_one)]
      exact hWupper omega)).trans hsumBound
  · exact (eLpNorm_mono_ae ((measurable_cutoffRatioSup M n (n + h) (Ch02.cubeDomain R)).aestronglyMeasurable) (Filter.Eventually.of_forall fun omega ↦ by
      have hpos : 0 < oneStepLowerSourceCellWeight M n h R omega := by
        unfold oneStepLowerSourceCellWeight
        exact cutoffRatioSup_pos M n (n + h) (Ch02.cubeDomain R) omega
      change ‖oneStepLowerSourceCellWeight M n h R omega‖ ≤ ‖W omega + 1‖
      rw [Real.norm_eq_abs, abs_of_pos
        hpos,
        Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hW0 omega) zero_le_one)]
      exact hWlower omega)).trans hsumBound

/-- A cutoff-ratio supremum may be inserted into the pointwise exponential
energy replacement using only an oscillation bound for a logarithmic
representative.  This avoids choosing a maximizer of the open-domain
supremum. -/
theorem cutoffRatioSup_cellEnergy_replacement
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (numerator denominator : ℕ) (U : Ch02.Domain d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (g : Vec d → ℝ) (osc : ℝ)
    (hg : ∀ y ∈ (U : Set (Vec d)),
      _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega y /
          _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega y = Real.exp (g y))
    (hosc : ∀ y ∈ (U : Set (Vec d)), ∀ x ∈ (U : Set (Vec d)),
      |g y - g x| ≤ osc)
    (p F : Vec d) {x : Vec d} (hx : x ∈ (U : Set (Vec d))) :
    |cutoffRatioSup M numerator denominator U omega * vecNormSq p -
        (_root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x) *
            vecNormSq (p + F)| ≤
      cutoffRatioSup M numerator denominator U omega *
        (osc * vecNormSq p +
          Real.sqrt (vecNormSq F) *
            Real.sqrt (vecNormSq (p + (p + F)))) := by
  let W := cutoffRatioSup M numerator denominator U omega
  have hWpos : 0 < W := cutoffRatioSup_pos M numerator denominator U omega
  have hpoint : Real.exp (g x) ≤ W := by
    rw [← hg x hx]
    exact cutoffRatio_le_cutoffRatioSup M numerator denominator U omega hx
  have hgxLog : g x ≤ Real.log W := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hWpos]
    exact hpoint
  have hWupper : W ≤ Real.exp (g x + osc) := by
    unfold W cutoffRatioSup
    apply csSup_le
    · obtain ⟨y, hy⟩ := U.nonempty
      exact ⟨_root_.SubdiffusiveProcess.Model.aCutoff M numerator omega y /
        _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega y, y, hy, rfl⟩
    · rintro r ⟨y, hy, rfl⟩
      rw [hg y hy]
      apply Real.exp_le_exp.mpr
      have hyx := hosc y hy x hx
      linarith [le_abs_self (g y - g x)]
  have hlogUpper : Real.log W ≤ g x + osc := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hWpos]
    exact hWupper
  have hdiff : |Real.log W - g x| ≤ osc := by
    rw [abs_of_nonneg (sub_nonneg.mpr hgxLog)]
    linarith
  have hrepl := oneStep_exp_cellEnergy_replacement
    (Real.log W) (g x) p F
  rw [max_eq_left hgxLog, Real.exp_log hWpos] at hrepl
  have hfirst := mul_le_mul_of_nonneg_right hdiff (vecNormSq_nonneg p)
  have hsum := add_le_add hfirst
    (le_refl (Real.sqrt (vecNormSq F) *
      Real.sqrt (vecNormSq (p + (p + F)))))
  have hW0 : 0 ≤ W := hWpos.le
  calc
    |W * vecNormSq p -
        (_root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x) *
            vecNormSq (p + F)| =
        |W * vecNormSq p - Real.exp (g x) * vecNormSq (p + F)| := by
          rw [hg x hx]
    _ ≤ W *
        (|Real.log W - g x| * vecNormSq p +
          Real.sqrt (vecNormSq F) *
            Real.sqrt (vecNormSq (p + (p + F)))) := hrepl
    _ ≤ W *
        (osc * vecNormSq p +
          Real.sqrt (vecNormSq F) *
            Real.sqrt (vecNormSq (p + (p + F)))) :=
      mul_le_mul_of_nonneg_left hsum hW0

/-- Forward source-cell specialization with the literal centered shell. -/
theorem oneStepUpperSourceCellWeight_cellEnergy_replacement
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (osc : ℝ) (hh : 0 < h)
    (hosc : ∀ y ∈ openCubeSet R, ∀ x ∈ openCubeSet R,
      |oneStepCenteredShellAt M n h y omega -
        oneStepCenteredShellAt M n h x omega| ≤ osc)
    (p F : Vec d) {x : Vec d} (hx : x ∈ openCubeSet R) :
    |oneStepUpperSourceCellWeight M n h R omega * vecNormSq p -
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (p + F)| ≤
      oneStepUpperSourceCellWeight M n h R omega *
        (osc * vecNormSq p +
          Real.sqrt (vecNormSq F) *
            Real.sqrt (vecNormSq (p + (p + F)))) := by
  have hg' : ∀ y ∈ ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d)),
      _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega y /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega y =
        Real.exp (oneStepCenteredShellAt M n h y omega) := by
    intro y hy
    have hrepr := cutoffRatioMinusOne_eq_exp_shell
      M (n + h) (n : ℤ) omega y (by omega)
        (by exact_mod_cast Nat.lt_add_of_pos_right hh)
    unfold cutoffRatioMinusOne aCutoffAtInt at hrepr
    simp only [show ¬ (n : ℤ) < 0 by omega, ite_false] at hrepr
    simp only [Int.toNat_natCast] at hrepr
    dsimp only [oneStepCenteredShellAt]
    have hgap : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
      push_cast
      ring_nf
    rw [hgap] at hrepr
    calc
      _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega y /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega y =
          (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega y /
            _root_.SubdiffusiveProcess.Model.aCutoff M n omega y - 1) + 1 := by
              ring_nf
      _ = (Real.exp (cutoffShellSum (n + h) (n : ℤ) y omega -
          (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) + 1 := by
            rw [hrepr]
      _ = Real.exp (oneStepCenteredShellAt M n h y omega) := by
        dsimp only [oneStepCenteredShellAt]
        rw [sub_add_cancel]
  have hosc' : ∀ y ∈ ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d)),
      ∀ x ∈ ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d)),
        |oneStepCenteredShellAt M n h y omega -
          oneStepCenteredShellAt M n h x omega| ≤ osc := by
    intro y hy x hx'
    exact hosc y (by simpa only [Ch02.cubeDomain_coe] using! hy)
      x (by simpa only [Ch02.cubeDomain_coe] using! hx')
  have hbase := cutoffRatioSup_cellEnergy_replacement M (n + h) n
    (Ch02.cubeDomain R) omega (oneStepCenteredShellAt M n h · omega)
      osc hg' hosc' p F (by simpa only [Ch02.cubeDomain_coe] using! hx)
  rw [hg' x (by simpa only [Ch02.cubeDomain_coe] using! hx)] at hbase
  simpa only [oneStepUpperSourceCellWeight] using! hbase



theorem oneStepLowerSourceCellWeight_cellEnergy_replacement
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (osc : ℝ) (hh : 0 < h)
    (hosc : ∀ y ∈ openCubeSet R, ∀ x ∈ openCubeSet R,
      |oneStepCenteredShellAt M n h y omega -
        oneStepCenteredShellAt M n h x omega| ≤ osc)
    (q G : Vec d) {x : Vec d} (hx : x ∈ openCubeSet R) :
    |oneStepLowerSourceCellWeight M n h R omega * vecNormSq q -
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (q + G)| ≤
      oneStepLowerSourceCellWeight M n h R omega *
        (osc * vecNormSq q +
          Real.sqrt (vecNormSq G) *
            Real.sqrt (vecNormSq (q + (q + G)))) := by
  have hg' : ∀ y ∈ ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d)),
      _root_.SubdiffusiveProcess.Model.aCutoff M n omega y /
          _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega y =
        Real.exp (-oneStepCenteredShellAt M n h y omega) := by
    intro y hy
    have hrepr := inverseCutoffRatioMinusOne_eq_exp_shell
      M (n + h) (n : ℤ) omega y (by omega)
        (by exact_mod_cast Nat.lt_add_of_pos_right hh)
    unfold inverseCutoffRatioMinusOne aCutoffAtInt at hrepr
    simp only [show ¬ (n : ℤ) < 0 by omega, ite_false] at hrepr
    simp only [Int.toNat_natCast] at hrepr
    dsimp only [oneStepCenteredShellAt]
    have hgap : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
      push_cast
      ring_nf
    rw [hgap] at hrepr
    calc
      _root_.SubdiffusiveProcess.Model.aCutoff M n omega y /
          _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega y =
          (_root_.SubdiffusiveProcess.Model.aCutoff M n omega y /
            _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega y - 1) + 1 := by
              ring_nf
      _ = (Real.exp (-cutoffShellSum (n + h) (n : ℤ) y omega +
          (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) + 1 := by
            rw [hrepr]
      _ = Real.exp (-oneStepCenteredShellAt M n h y omega) := by
        dsimp only [oneStepCenteredShellAt]
        rw [sub_add_cancel]
        apply Real.exp_injective
        ring_nf
  have hosc' : ∀ y ∈ ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d)),
      ∀ x ∈ ((Ch02.cubeDomain R : Ch02.Domain d) : Set (Vec d)),
        |(-oneStepCenteredShellAt M n h · omega) y -
          (-oneStepCenteredShellAt M n h · omega) x| ≤ osc := by
    intro y hy x hx'
    simpa only [Pi.neg_apply, abs_neg, neg_sub_neg, abs_sub_comm] using!
      hosc y (by simpa only [Ch02.cubeDomain_coe] using! hy)
        x (by simpa only [Ch02.cubeDomain_coe] using! hx')
  have hbase := cutoffRatioSup_cellEnergy_replacement M n (n + h)
    (Ch02.cubeDomain R) omega (-oneStepCenteredShellAt M n h · omega)
      osc hg' hosc' q G (by simpa only [Ch02.cubeDomain_coe] using! hx)
  rw [hg' x (by simpa only [Ch02.cubeDomain_coe] using! hx)] at hbase
  simpa only [oneStepLowerSourceCellWeight] using! hbase

/-- Literal source-cell forward replacement with its measurable oscillation
envelope inserted. -/
theorem oneStepUpperSourceCellWeight_cellEnergy_replacement_of_sourceCell
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (p F : Vec d) {x : Vec d} (hx : x ∈ openCubeSet R) :
    |oneStepUpperSourceCellWeight M n h R omega * vecNormSq p -
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (p + F)| ≤
      oneStepUpperSourceCellWeight M n h R omega *
        (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
            vecNormSq p +
          Real.sqrt (vecNormSq F) *
            Real.sqrt (vecNormSq (p + (p + F)))) := by
  have hscaleEq := oneStepSourceCells_scale_eq hK hR
  have hscale : R.scale ≤ (n : ℤ) := by
    rw [hscaleEq]
    exact_mod_cast Nat.sub_le n (oneStepLocalizationDepth M.delta)
  exact oneStepUpperSourceCellWeight_cellEnergy_replacement
    M n h R omega
      (2 * oneStepSourceCellShellOscillationEnvelope n h R omega) hh
      (fun y hy x hx' ↦
        abs_oneStepCenteredShellAt_sub_le_two_envelope
          M n h R omega hscale hx' hy)
      p F hx

/-- Reciprocal source-cell replacement with the same measurable envelope. -/
theorem oneStepLowerSourceCellWeight_cellEnergy_replacement_of_sourceCell
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (q G : Vec d) {x : Vec d} (hx : x ∈ openCubeSet R) :
    |oneStepLowerSourceCellWeight M n h R omega * vecNormSq q -
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (q + G)| ≤
      oneStepLowerSourceCellWeight M n h R omega *
        (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
            vecNormSq q +
          Real.sqrt (vecNormSq G) *
            Real.sqrt (vecNormSq (q + (q + G)))) := by
  have hscaleEq := oneStepSourceCells_scale_eq hK hR
  have hscale : R.scale ≤ (n : ℤ) := by
    rw [hscaleEq]
    exact_mod_cast Nat.sub_le n (oneStepLocalizationDepth M.delta)
  exact oneStepLowerSourceCellWeight_cellEnergy_replacement
    M n h R omega
      (2 * oneStepSourceCellShellOscillationEnvelope n h R omega) hh
      (fun y hy x hx' ↦
        abs_oneStepCenteredShellAt_sub_le_two_envelope
          M n h R omega hscale hx' hy)
      q G hx

/-! ## Normalized spatial replacement -/

/-- Integrate a pointwise replacement estimate on a normalized cube.  This
small measure-theoretic wrapper is deliberately independent of the GMC
fields: it lets both source-cell lanes retain the same deterministic
majorant through the spatial average. -/
theorem abs_const_sub_cubeAverage_le_cubeAverage_of_pointwise
    {d : ℕ} (R : TriadicCube d) (c : ℝ) (energy majorant : Vec d → ℝ)
    (henergy : Integrable energy (normalizedCubeMeasure R))
    (hmajorant : Integrable majorant (normalizedCubeMeasure R))
    (hpoint : ∀ᵐ x ∂normalizedCubeMeasure R,
      |c - energy x| ≤ majorant x) :
    |c - cubeAverage R energy| ≤ cubeAverage R majorant := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  have hc : Integrable (fun _ : Vec d ↦ c) (normalizedCubeMeasure R) :=
    integrable_const c
  calc
    |c - ∫ x, energy x ∂normalizedCubeMeasure R| =
        |∫ x, c - energy x ∂normalizedCubeMeasure R| := by
      rw [integral_sub hc henergy, integral_const]
      rw [Measure.real_def, normalizedCubeMeasure_apply_univ]
      simp
    _ ≤ ∫ x, |c - energy x| ∂normalizedCubeMeasure R :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, majorant x ∂normalizedCubeMeasure R := by
      exact integral_mono_ae (hc.sub henergy).abs hmajorant hpoint

/-- Spatially averaged forward replacement on a literal source cell.  The
two integrability hypotheses are stated explicitly so callers may use the
canonical Sobolev representatives without changing them on a null set. -/
theorem oneStepUpperSourceCellWeight_cubeAverage_replacement
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (p : Vec d) (F : Vec d → Vec d)
    (henergy : Integrable (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega) *
        vecNormSq (p + F x)) (normalizedCubeMeasure R))
    (hmajorant : Integrable (fun x ↦
      oneStepUpperSourceCellWeight M n h R omega *
        (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
            vecNormSq p +
          Real.sqrt (vecNormSq (F x)) *
            Real.sqrt (vecNormSq (p + (p + F x)))))
      (normalizedCubeMeasure R)) :
    |oneStepUpperSourceCellWeight M n h R omega * vecNormSq p -
        cubeAverage R (fun x ↦
          Real.exp (oneStepCenteredShellAt M n h x omega) *
            vecNormSq (p + F x))| ≤
      cubeAverage R (fun x ↦
        oneStepUpperSourceCellWeight M n h R omega *
          (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
              vecNormSq p +
            Real.sqrt (vecNormSq (F x)) *
              Real.sqrt (vecNormSq (p + (p + F x))))) := by
  apply abs_const_sub_cubeAverage_le_cubeAverage_of_pointwise
    R (oneStepUpperSourceCellWeight M n h R omega * vecNormSq p)
      _ _ henergy hmajorant
  apply Gagliardo.ae_normalizedCubeMeasure_iff.2
  rw [cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
  exact oneStepUpperSourceCellWeight_cellEnergy_replacement_of_sourceCell
    M n h R omega hK hR hh p (F x) hx

/-- Reciprocal averaged replacement, with the same normalized majorant. -/
theorem oneStepLowerSourceCellWeight_cubeAverage_replacement
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (q : Vec d) (G : Vec d → Vec d)
    (henergy : Integrable (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq (q + G x)) (normalizedCubeMeasure R))
    (hmajorant : Integrable (fun x ↦
      oneStepLowerSourceCellWeight M n h R omega *
        (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
            vecNormSq q +
          Real.sqrt (vecNormSq (G x)) *
            Real.sqrt (vecNormSq (q + (q + G x)))))
      (normalizedCubeMeasure R)) :
    |oneStepLowerSourceCellWeight M n h R omega * vecNormSq q -
        cubeAverage R (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (q + G x))| ≤
      cubeAverage R (fun x ↦
        oneStepLowerSourceCellWeight M n h R omega *
          (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
              vecNormSq q +
            Real.sqrt (vecNormSq (G x)) *
              Real.sqrt (vecNormSq (q + (q + G x))))) := by
  apply abs_const_sub_cubeAverage_le_cubeAverage_of_pointwise
    R (oneStepLowerSourceCellWeight M n h R omega * vecNormSq q)
      _ _ henergy hmajorant
  apply Gagliardo.ae_normalizedCubeMeasure_iff.2
  rw [cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
  exact oneStepLowerSourceCellWeight_cellEnergy_replacement_of_sourceCell
    M n h R omega hK hR hh q (G x) hx

/-! ## Automatic integrability for the canonical cell fields -/

/-- The literal exponential shell ratio is bounded by the forward source
weight at every point of the cell. -/
theorem exp_oneStepCenteredShellAt_le_upperSourceCellWeight
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    Real.exp (oneStepCenteredShellAt M n h x omega) ≤
      oneStepUpperSourceCellWeight M n h R omega := by
  have hrepr := cutoffRatioMinusOne_eq_exp_shell
    M (n + h) (n : ℤ) omega x (by omega)
      (by exact_mod_cast Nat.lt_add_of_pos_right hh)
  unfold cutoffRatioMinusOne aCutoffAtInt at hrepr
  simp only [show ¬ (n : ℤ) < 0 by omega, ite_false,
    Int.toNat_natCast] at hrepr
  have hgap : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
    push_cast
    ring_nf
  rw [hgap] at hrepr
  have heq :
      _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega x =
        Real.exp (oneStepCenteredShellAt M n h x omega) := by
    calc
      _ = (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega x - 1) + 1 := by ring
      _ = (Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) + 1 := by
            rw [hrepr]
      _ = _ := by
        dsimp only [oneStepCenteredShellAt]
        rw [sub_add_cancel]
  rw [← heq]
  exact cutoffRatio_le_oneStepUpperSourceCellWeight M n h R omega hx

/-- Reciprocal pointwise shell ratio bound. -/
theorem exp_neg_oneStepCenteredShellAt_le_lowerSourceCellWeight
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    Real.exp (-oneStepCenteredShellAt M n h x omega) ≤
      oneStepLowerSourceCellWeight M n h R omega := by
  have hrepr := inverseCutoffRatioMinusOne_eq_exp_shell
    M (n + h) (n : ℤ) omega x (by omega)
      (by exact_mod_cast Nat.lt_add_of_pos_right hh)
  unfold inverseCutoffRatioMinusOne aCutoffAtInt at hrepr
  simp only [show ¬ (n : ℤ) < 0 by omega, ite_false,
    Int.toNat_natCast] at hrepr
  have hgap : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
    push_cast
    ring_nf
  rw [hgap] at hrepr
  have heq :
      _root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x =
        Real.exp (-oneStepCenteredShellAt M n h x omega) := by
    calc
      _ = (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x - 1) + 1 := by ring
      _ = (Real.exp (-cutoffShellSum (n + h) (n : ℤ) x omega +
          (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) + 1 := by
            rw [hrepr]
      _ = _ := by
        dsimp only [oneStepCenteredShellAt]
        rw [sub_add_cancel]
        apply Real.exp_injective
        ring_nf
  rw [← heq]
  exact cutoffRatio_le_oneStepLowerSourceCellWeight M n h R omega hx

/-- A vector-valued `L²` field has integrable Euclidean square norm. -/
theorem integrable_vecNormSq_of_memLp_two
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {F : Omega → Vec d} (hF : MemLp F 2 mu) :
    Integrable (fun omega ↦ vecNormSq (F omega)) mu := by
  have hsum := integrable_finsetSum (μ := mu) Finset.univ
    (f := fun (i : Fin d) omega ↦ F omega i ^ 2) fun i _ ↦
      (hF.continuousLinearMap_comp
        (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)).integrable_sq
  exact hsum.congr (Filter.Eventually.of_forall fun omega ↦ by
    simp [vecNormSq, vecDot, pow_two])

private theorem integrable_sqrt_vecNormSq_mul_of_memLp_two
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {F G : Omega → Vec d} (hF : MemLp F 2 mu) (hG : MemLp G 2 mu) :
    Integrable (fun omega ↦
      Real.sqrt (vecNormSq (F omega)) *
        Real.sqrt (vecNormSq (G omega))) mu := by
  have hFsq := integrable_vecNormSq_of_memLp_two hF
  have hGsq := integrable_vecNormSq_of_memLp_two hG
  refine Integrable.mono' ((hFsq.add hGsq).div_const 2) ?_ ?_
  · exact (Real.continuous_sqrt.comp_aestronglyMeasurable hFsq.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hGsq.1)
  · filter_upwards with omega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact sqrt_mul_sqrt_le_half_add
      (vecNormSq_nonneg _) (vecNormSq_nonneg _)

/-- Spatial measurability of the centered shell block at a fixed sample. -/
theorem measurable_oneStepCenteredShellAt_space
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Measurable (fun x ↦ oneStepCenteredShellAt M n h x omega) := by
  unfold oneStepCenteredShellAt cutoffShellSum
  exact (Finset.measurable_sum _ fun j _ ↦ (omega j).1.1.continuous.measurable)
    |>.sub measurable_const

/-- The two spatial integrability premises of the forward averaged
replacement follow from a single normalized `L²` certificate for the cell
fluctuation. -/
theorem oneStepUpperSourceCellWeight_cubeAverage_replacement_of_memLp
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (p : Vec d) (F : Vec d → Vec d)
    (hF : MemLp F 2 (normalizedCubeMeasure R)) :
    |oneStepUpperSourceCellWeight M n h R omega * vecNormSq p -
        cubeAverage R (fun x ↦
          Real.exp (oneStepCenteredShellAt M n h x omega) *
            vecNormSq (p + F x))| ≤
      cubeAverage R (fun x ↦
        oneStepUpperSourceCellWeight M n h R omega *
          (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
              vecNormSq p +
            Real.sqrt (vecNormSq (F x)) *
              Real.sqrt (vecNormSq (p + (p + F x))))) := by
  let W := oneStepUpperSourceCellWeight M n h R omega
  have hW0 : 0 ≤ W := by
    dsimp only [W, oneStepUpperSourceCellWeight]
    exact (cutoffRatioSup_pos M (n + h) n (Ch02.cubeDomain R) omega).le
  have hPF : MemLp (fun x ↦ p + F x) 2 (normalizedCubeMeasure R) := by
    simpa only [Pi.add_apply] using! (memLp_const p).add hF
  have hPPF : MemLp (fun x ↦ p + (p + F x)) 2
      (normalizedCubeMeasure R) := by
    simpa only [Pi.add_apply] using! (memLp_const p).add hPF
  have hsq := integrable_vecNormSq_of_memLp_two hPF
  have henergyMeas : AEStronglyMeasurable (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega) *
        vecNormSq (p + F x)) (normalizedCubeMeasure R) :=
    ((Real.measurable_exp.comp
      (measurable_oneStepCenteredShellAt_space M n h omega)).aestronglyMeasurable
      |>.mul hsq.1)
  have henergy : Integrable (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega) *
        vecNormSq (p + F x)) (normalizedCubeMeasure R) := by
    refine (hsq.const_mul W).mono' henergyMeas ?_
    apply Gagliardo.ae_normalizedCubeMeasure_iff.2
    rw [cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (vecNormSq_nonneg _))]
    change Real.exp (oneStepCenteredShellAt M n h x omega) *
      vecNormSq (p + F x) ≤
        oneStepUpperSourceCellWeight M n h R omega * vecNormSq (p + F x)
    exact mul_le_mul_of_nonneg_right
      (exp_oneStepCenteredShellAt_le_upperSourceCellWeight
        M n h R omega hh hx) (vecNormSq_nonneg _)
  have hproduct := integrable_sqrt_vecNormSq_mul_of_memLp_two hF hPPF
  have hmajorant : Integrable (fun x ↦
      W * (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
          vecNormSq p +
        Real.sqrt (vecNormSq (F x)) *
          Real.sqrt (vecNormSq (p + (p + F x)))))
      (normalizedCubeMeasure R) :=
    ((integrable_const
      (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
        vecNormSq p)).add hproduct).const_mul W
  exact oneStepUpperSourceCellWeight_cubeAverage_replacement
    M n h R omega hK hR hh p F henergy (by simpa only [W] using! hmajorant)

/-- Reciprocal automatic-integrability specialization. -/
theorem oneStepLowerSourceCellWeight_cubeAverage_replacement_of_memLp
    {d K : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h)
    (q : Vec d) (G : Vec d → Vec d)
    (hG : MemLp G 2 (normalizedCubeMeasure R)) :
    |oneStepLowerSourceCellWeight M n h R omega * vecNormSq q -
        cubeAverage R (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (q + G x))| ≤
      cubeAverage R (fun x ↦
        oneStepLowerSourceCellWeight M n h R omega *
          (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
              vecNormSq q +
            Real.sqrt (vecNormSq (G x)) *
              Real.sqrt (vecNormSq (q + (q + G x))))) := by
  let W := oneStepLowerSourceCellWeight M n h R omega
  have hW0 : 0 ≤ W := by
    dsimp only [W, oneStepLowerSourceCellWeight]
    exact (cutoffRatioSup_pos M n (n + h) (Ch02.cubeDomain R) omega).le
  have hQG : MemLp (fun x ↦ q + G x) 2 (normalizedCubeMeasure R) := by
    simpa only [Pi.add_apply] using! (memLp_const q).add hG
  have hQQG : MemLp (fun x ↦ q + (q + G x)) 2
      (normalizedCubeMeasure R) := by
    simpa only [Pi.add_apply] using! (memLp_const q).add hQG
  have hsq := integrable_vecNormSq_of_memLp_two hQG
  have henergyMeas : AEStronglyMeasurable (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq (q + G x)) (normalizedCubeMeasure R) :=
    ((Real.measurable_exp.comp
      (measurable_oneStepCenteredShellAt_space M n h omega).neg)
      |>.aestronglyMeasurable.mul hsq.1)
  have henergy : Integrable (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq (q + G x)) (normalizedCubeMeasure R) := by
    refine (hsq.const_mul W).mono' henergyMeas ?_
    apply Gagliardo.ae_normalizedCubeMeasure_iff.2
    rw [cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (vecNormSq_nonneg _))]
    change Real.exp (-oneStepCenteredShellAt M n h x omega) *
      vecNormSq (q + G x) ≤
        oneStepLowerSourceCellWeight M n h R omega * vecNormSq (q + G x)
    exact mul_le_mul_of_nonneg_right
      (exp_neg_oneStepCenteredShellAt_le_lowerSourceCellWeight
        M n h R omega hh hx) (vecNormSq_nonneg _)
  have hproduct := integrable_sqrt_vecNormSq_mul_of_memLp_two hG hQQG
  have hmajorant : Integrable (fun x ↦
      W * (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
          vecNormSq q +
        Real.sqrt (vecNormSq (G x)) *
          Real.sqrt (vecNormSq (q + (q + G x)))))
      (normalizedCubeMeasure R) :=
    ((integrable_const
      (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
        vecNormSq q)).add hproduct).const_mul W
  exact oneStepLowerSourceCellWeight_cubeAverage_replacement
    M n h R omega hK hR hh q G henergy (by simpa only [W] using! hmajorant)

/-! ## Canonical source-cell slope specialization -/

/-- The primal large-cube slope restricts to normalized `L²` on every
source cell. -/
theorem oneStepDirichletSlopeField_memLp_sourceCell
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemLp
      (oneStepDirichletSlopeField M n h p
        (originCube d (K : ℤ)) omega hh)
      2 (normalizedCubeMeasure R) := by
  have hparent : MemLp
      (oneStepDirichletSlopeField M n h p
        (originCube d (K : ℤ)) omega hh)
      2 (normalizedCubeMeasure (originCube d (K : ℤ))) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet
      (originCube d (K : ℤ))
      (oneStepDirichletSlopeField_memVectorL2
        M n h p (originCube d (K : ℤ)) omega hh)
  exact memLp_on_descendant_of_memLp_generic
    (mem_oneStepSourceCells hR) hparent

/-- The dual large-cube slope restricts to normalized `L²` on every source
cell. -/
theorem oneStepNeumannSlopeField_memLp_sourceCell
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemLp
      (oneStepNeumannSlopeField M n h q
        (originCube d (K : ℤ)) omega hh)
      2 (normalizedCubeMeasure R) := by
  have hparent : MemLp
      (oneStepNeumannSlopeField M n h q
        (originCube d (K : ℤ)) omega hh)
      2 (normalizedCubeMeasure (originCube d (K : ℤ))) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet
      (originCube d (K : ℤ))
      (oneStepNeumannSlopeField_memVectorL2
        M n h q (originCube d (K : ℤ)) omega hh)
  exact memLp_on_descendant_of_memLp_generic
    (mem_oneStepSourceCells hR) hparent

/-- The centered primal source-cell fluctuation has the normalized `L²`
certificate required by the automatic replacement theorem. -/
theorem cubeFluctuationVec_oneStepDirichletSlopeField_memLp_sourceCell
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemLp
      (cubeFluctuationVec R
        (oneStepDirichletSlopeField M n h p
          (originCube d (K : ℤ)) omega hh))
      2 (normalizedCubeMeasure R) :=
  memLp_cubeFluctuationVec R _
    (oneStepDirichletSlopeField_memLp_sourceCell
      M n h p R hR omega hh)

/-- The centered dual source-cell fluctuation has the normalized `L²`
certificate required by the automatic replacement theorem. -/
theorem cubeFluctuationVec_oneStepNeumannSlopeField_memLp_sourceCell
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemLp
      (cubeFluctuationVec R
        (oneStepNeumannSlopeField M n h q
          (originCube d (K : ℤ)) omega hh))
      2 (normalizedCubeMeasure R) :=
  memLp_cubeFluctuationVec R _
    (oneStepNeumannSlopeField_memLp_sourceCell
      M n h q R hR omega hh)

/-- Literal primal source-cell replacement for the measurable Dirichlet
minimizer slope. -/
theorem oneStepDirichletSourceCell_cubeAverage_replacement
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    |oneStepUpperSourceCellWeight M n h R omega *
          vecNormSq (oneStepDirichletCellSlope M n h p
            (originCube d (K : ℤ)) R omega hh) -
        cubeAverage R (fun x ↦
          Real.exp (oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepDirichletSlopeField M n h p
              (originCube d (K : ℤ)) omega hh x))| ≤
      cubeAverage R (fun x ↦
        oneStepUpperSourceCellWeight M n h R omega *
          (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
              vecNormSq (oneStepDirichletCellSlope M n h p
                (originCube d (K : ℤ)) R omega hh) +
            Real.sqrt (vecNormSq (cubeFluctuationVec R
              (oneStepDirichletSlopeField M n h p
                (originCube d (K : ℤ)) omega hh) x)) *
              Real.sqrt (vecNormSq
                (oneStepDirichletCellSlope M n h p
                    (originCube d (K : ℤ)) R omega hh +
                  oneStepDirichletSlopeField M n h p
                    (originCube d (K : ℤ)) omega hh x)))) := by
  have hmean := oneStepDirichletCellSlope_eq_cubeAverageVec
    M n h p (originCube d (K : ℤ)) R
      (mem_oneStepSourceCells hR) omega hh
  have hbase :=
    oneStepUpperSourceCellWeight_cubeAverage_replacement_of_memLp
      M n h R omega hK hR hh
      (oneStepDirichletCellSlope M n h p
        (originCube d (K : ℤ)) R omega hh)
      (cubeFluctuationVec R
        (oneStepDirichletSlopeField M n h p
          (originCube d (K : ℤ)) omega hh))
      (cubeFluctuationVec_oneStepDirichletSlopeField_memLp_sourceCell
        M n h p R hR omega hh)
  have hreconstruct :
      (fun x ↦ cubeAverageVec R
          (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh) +
        cubeFluctuationVec R
          (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh) x) =
        oneStepDirichletSlopeField M n h p
          (originCube d (K : ℤ)) omega hh := by
    funext x
    simp only [cubeFluctuationVec_apply]
    abel
  rw [hmean] at hbase ⊢
  have hreconstruct_at (x : Vec d) :
      cubeAverageVec R
          (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh) +
        cubeFluctuationVec R
          (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh) x =
        oneStepDirichletSlopeField M n h p
          (originCube d (K : ℤ)) omega hh x :=
    congrFun hreconstruct x
  simp_rw [hreconstruct_at] at hbase
  exact hbase

/-- Literal dual source-cell replacement for the measurable Neumann
minimizer slope. -/
theorem oneStepNeumannSourceCell_cubeAverage_replacement
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    |oneStepLowerSourceCellWeight M n h R omega *
          vecNormSq (oneStepNeumannCellSlope M n h q
            (originCube d (K : ℤ)) R omega hh) -
        cubeAverage R (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepNeumannSlopeField M n h q
              (originCube d (K : ℤ)) omega hh x))| ≤
      cubeAverage R (fun x ↦
        oneStepLowerSourceCellWeight M n h R omega *
          (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
              vecNormSq (oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh) +
            Real.sqrt (vecNormSq (cubeFluctuationVec R
              (oneStepNeumannSlopeField M n h q
                (originCube d (K : ℤ)) omega hh) x)) *
              Real.sqrt (vecNormSq
                (oneStepNeumannCellSlope M n h q
                    (originCube d (K : ℤ)) R omega hh +
                  oneStepNeumannSlopeField M n h q
                    (originCube d (K : ℤ)) omega hh x)))) := by
  have hmean := oneStepNeumannCellSlope_eq_cubeAverageVec
    M n h q (originCube d (K : ℤ)) R
      (mem_oneStepSourceCells hR) omega hh
  have hbase :=
    oneStepLowerSourceCellWeight_cubeAverage_replacement_of_memLp
      M n h R omega hK hR hh
      (oneStepNeumannCellSlope M n h q
        (originCube d (K : ℤ)) R omega hh)
      (cubeFluctuationVec R
        (oneStepNeumannSlopeField M n h q
          (originCube d (K : ℤ)) omega hh))
      (cubeFluctuationVec_oneStepNeumannSlopeField_memLp_sourceCell
        M n h q R hR omega hh)
  have hreconstruct :
      (fun x ↦ cubeAverageVec R
          (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh) +
        cubeFluctuationVec R
          (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh) x) =
        oneStepNeumannSlopeField M n h q
          (originCube d (K : ℤ)) omega hh := by
    funext x
    simp only [cubeFluctuationVec_apply]
    abel
  rw [hmean] at hbase ⊢
  have hreconstruct_at (x : Vec d) :
      cubeAverageVec R
          (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh) +
        cubeFluctuationVec R
          (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh) x =
        oneStepNeumannSlopeField M n h q
          (originCube d (K : ℤ)) omega hh x :=
    congrFun hreconstruct x
  simp_rw [hreconstruct_at] at hbase
  exact hbase

/-! ## Normalized source-family junction -/

/-- The nonnegative primal replacement envelope on one literal source
cell. -/
def oneStepDirichletSourceCellReplacementError
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (R : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  cubeAverage R (fun x ↦
    oneStepUpperSourceCellWeight M n h R omega *
      (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
          vecNormSq (oneStepDirichletCellSlope M n h p
            (originCube d (K : ℤ)) R omega hh) +
        Real.sqrt (vecNormSq (cubeFluctuationVec R
          (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh) x)) *
          Real.sqrt (vecNormSq
            (oneStepDirichletCellSlope M n h p
                (originCube d (K : ℤ)) R omega hh +
              oneStepDirichletSlopeField M n h p
                (originCube d (K : ℤ)) omega hh x))))

/-- The reciprocal replacement envelope on one source cell. -/
def oneStepNeumannSourceCellReplacementError
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  cubeAverage R (fun x ↦
    oneStepLowerSourceCellWeight M n h R omega *
      (2 * oneStepSourceCellShellOscillationEnvelope n h R omega *
          vecNormSq (oneStepNeumannCellSlope M n h q
            (originCube d (K : ℤ)) R omega hh) +
        Real.sqrt (vecNormSq (cubeFluctuationVec R
          (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh) x)) *
          Real.sqrt (vecNormSq
            (oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh +
              oneStepNeumannSlopeField M n h q
                (originCube d (K : ℤ)) omega hh x))))

/-- The source-family weighted primal means are bounded by the literal
weighted full slopes plus the normalized sum of replacement envelopes. -/
theorem normalized_sum_oneStepDirichletSourceCellWeight_le
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d)
    (hK : oneStepLocalizationScale n M.delta ≤ K) (hh : 0 < h)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepUpperSourceCellWeight M n h R omega *
            vecNormSq (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh) ≤
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          (cubeAverage R (fun x ↦
              Real.exp (oneStepCenteredShellAt M n h x omega) *
                vecNormSq (oneStepDirichletSlopeField M n h p
                  (originCube d (K : ℤ)) omega hh x)) +
            oneStepDirichletSourceCellReplacementError
              (K := K) M n h p R omega hh) := by
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro R hR
    have hcell := oneStepDirichletSourceCell_cubeAverage_replacement
      M n h p R hK hR omega hh
    have hle := (le_abs_self
      (oneStepUpperSourceCellWeight M n h R omega *
          vecNormSq (oneStepDirichletCellSlope M n h p
            (originCube d (K : ℤ)) R omega hh) -
        cubeAverage R (fun x ↦
          Real.exp (oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepDirichletSlopeField M n h p
              (originCube d (K : ℤ)) omega hh x)))).trans hcell
    dsimp only [oneStepDirichletSourceCellReplacementError]
    linarith
  · positivity

/-- Dual normalized source-family junction. -/
theorem normalized_sum_oneStepNeumannSourceCellWeight_le
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d)
    (hK : oneStepLocalizationScale n M.delta ≤ K) (hh : 0 < h)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh) ≤
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          (cubeAverage R (fun x ↦
              Real.exp (-oneStepCenteredShellAt M n h x omega) *
                vecNormSq (oneStepNeumannSlopeField M n h q
                  (originCube d (K : ℤ)) omega hh x)) +
            oneStepNeumannSourceCellReplacementError
              (K := K) M n h q R omega hh) := by
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro R hR
    have hcell := oneStepNeumannSourceCell_cubeAverage_replacement
      M n h q R hK hR omega hh
    have hle := (le_abs_self
      (oneStepLowerSourceCellWeight M n h R omega *
          vecNormSq (oneStepNeumannCellSlope M n h q
            (originCube d (K : ℤ)) R omega hh) -
        cubeAverage R (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepNeumannSlopeField M n h q
              (originCube d (K : ℤ)) omega hh x)))).trans hcell
    dsimp only [oneStepNeumannSourceCellReplacementError]
    linarith
  · positivity

/-- Exact collapse of the literal source partition to the parent normalized
cube average. -/
theorem normalized_sum_sourceCells_cubeAverage_eq_parent
    {d K n : ℕ} {delta : ℝ} (f : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet (originCube d (K : ℤ))) volume) :
    (((oneStepSourceCells d K n delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n delta, cubeAverage R f =
      cubeAverage (originCube d (K : ℤ)) f := by
  simpa only [oneStepSourceCells, descendantsAverage] using!
    (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      (originCube d (K : ℤ))
      (K - oneStepLocalizationScale n delta) f hf).symm

/-- The literal primal weighted full-slope energy is integrable on the
parent cube, so the exact source-partition identity applies to it. -/
theorem integrableOn_oneStepDirichletWeightedSlope_parent
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    IntegrableOn (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega) *
        vecNormSq (oneStepDirichletSlopeField M n h p
          (originCube d (K : ℤ)) omega hh x))
      (cubeSet (originCube d (K : ℤ))) volume := by
  let Q := originCube d (K : ℤ)
  let F := oneStepDirichletSlopeField M n h p Q omega hh
  have hF : MemLp F 2 (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh)
  have hsq := integrable_vecNormSq_of_memLp_two hF
  let W := oneStepUpperSourceCellWeight M n h Q omega
  have henergyMeas : AEStronglyMeasurable (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega) * vecNormSq (F x))
      (normalizedCubeMeasure Q) :=
    ((Real.measurable_exp.comp
      (measurable_oneStepCenteredShellAt_space M n h omega)).aestronglyMeasurable
      |>.mul hsq.1)
  have henergy : Integrable (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega) * vecNormSq (F x))
      (normalizedCubeMeasure Q) := by
    refine (hsq.const_mul W).mono' henergyMeas ?_
    apply Gagliardo.ae_normalizedCubeMeasure_iff.2
    rw [cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (vecNormSq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (exp_oneStepCenteredShellAt_le_upperSourceCellWeight
        M n h Q omega hh hx) (vecNormSq_nonneg _)
  have hc0 : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  have hctop : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hcube : Integrable (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega) * vecNormSq (F x))
      (cubeMeasure Q) :=
    (integrable_smul_measure hc0 hctop).mp (by
      simpa only [normalizedCubeMeasure] using! henergy)
  simpa only [Q, F, cubeMeasure] using! hcube

/-- Reciprocal weighted full-slope integrability on the parent cube. -/
theorem integrableOn_oneStepNeumannWeightedSlope_parent
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    IntegrableOn (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq (oneStepNeumannSlopeField M n h q
          (originCube d (K : ℤ)) omega hh x))
      (cubeSet (originCube d (K : ℤ))) volume := by
  let Q := originCube d (K : ℤ)
  let F := oneStepNeumannSlopeField M n h q Q omega hh
  have hF : MemLp F 2 (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh)
  have hsq := integrable_vecNormSq_of_memLp_two hF
  let W := oneStepLowerSourceCellWeight M n h Q omega
  have henergyMeas : AEStronglyMeasurable (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) * vecNormSq (F x))
      (normalizedCubeMeasure Q) :=
    ((Real.measurable_exp.comp
      (measurable_oneStepCenteredShellAt_space M n h omega).neg)
      |>.aestronglyMeasurable.mul hsq.1)
  have henergy : Integrable (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) * vecNormSq (F x))
      (normalizedCubeMeasure Q) := by
    refine (hsq.const_mul W).mono' henergyMeas ?_
    apply Gagliardo.ae_normalizedCubeMeasure_iff.2
    rw [cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (vecNormSq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (exp_neg_oneStepCenteredShellAt_le_lowerSourceCellWeight
        M n h Q omega hh hx) (vecNormSq_nonneg _)
  have hc0 : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  have hctop : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hcube : Integrable (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) * vecNormSq (F x))
      (cubeMeasure Q) :=
    (integrable_smul_measure hc0 hctop).mp (by
      simpa only [normalizedCubeMeasure] using! henergy)
  simpa only [Q, F, cubeMeasure] using! hcube

/-- Exact primal collapse for the concrete measurable parent solution. -/
theorem normalized_sum_oneStepDirichletWeightedSlope_eq_parent
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          cubeAverage R (fun x ↦
            Real.exp (oneStepCenteredShellAt M n h x omega) *
              vecNormSq (oneStepDirichletSlopeField M n h p
                (originCube d (K : ℤ)) omega hh x)) =
      cubeAverage (originCube d (K : ℤ)) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh x)) :=
  normalized_sum_sourceCells_cubeAverage_eq_parent _
    (integrableOn_oneStepDirichletWeightedSlope_parent
      M n h p omega hh)

/-- Exact reciprocal collapse for the concrete Neumann solution. -/
theorem normalized_sum_oneStepNeumannWeightedSlope_eq_parent
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          cubeAverage R (fun x ↦
            Real.exp (-oneStepCenteredShellAt M n h x omega) *
              vecNormSq (oneStepNeumannSlopeField M n h q
                (originCube d (K : ℤ)) omega hh x)) =
      cubeAverage (originCube d (K : ℤ)) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh x)) :=
  normalized_sum_sourceCells_cubeAverage_eq_parent _
    (integrableOn_oneStepNeumannWeightedSlope_parent
      M n h q omega hh)

/-- Final samplewise primal source-partition comparison.  The full-slope
part has been collapsed to the parent cube; only the explicit measurable
replacement envelopes remain cellwise. -/
theorem normalized_sum_oneStepDirichletSourceCellWeight_le_parent_add_error
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepUpperSourceCellWeight M n h R omega *
            vecNormSq (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh) ≤
      cubeAverage (originCube d (K : ℤ)) (fun x ↦
          Real.exp (oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepDirichletSlopeField M n h p
              (originCube d (K : ℤ)) omega hh x)) +
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            oneStepDirichletSourceCellReplacementError
              (K := K) M n h p R omega hh := by
  have hraw := normalized_sum_oneStepDirichletSourceCellWeight_le
    M n h p hK hh omega
  rw [Finset.sum_congr rfl (fun R _ ↦ by rfl),
    Finset.sum_add_distrib, mul_add] at hraw
  rw [normalized_sum_oneStepDirichletWeightedSlope_eq_parent
    M n h p omega hh] at hraw
  exact hraw

/-- Final samplewise reciprocal source-partition comparison. -/
theorem normalized_sum_oneStepNeumannSourceCellWeight_le_parent_add_error
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (q : Vec d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh) ≤
      cubeAverage (originCube d (K : ℤ)) (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepNeumannSlopeField M n h q
              (originCube d (K : ℤ)) omega hh x)) +
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            oneStepNeumannSourceCellReplacementError
              (K := K) M n h q R omega hh := by
  have hraw := normalized_sum_oneStepNeumannSourceCellWeight_le
    M n h q hK hh omega
  rw [Finset.sum_congr rfl (fun R _ ↦ by rfl),
    Finset.sum_add_distrib, mul_add] at hraw
  rw [normalized_sum_oneStepNeumannWeightedSlope_eq_parent
    M n h q omega hh] at hraw
  exact hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
