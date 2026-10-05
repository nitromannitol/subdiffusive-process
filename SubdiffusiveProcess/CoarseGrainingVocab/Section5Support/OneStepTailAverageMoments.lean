module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.ResponseObservableMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticitySpecialization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepEllipticityFactorMoment

@[expose] public section

/-!
# Moments of the one-step tail cube average

The weighted Section 4 ellipticity observable is normalized by the random
cube average of the suffix coefficient.  This file removes that normalization
using the already proved spatial cutoff-ratio moments.  The only analytic
input is Jensen on the normalized cube measure, in both the direct and
reciprocal orientations.
-/

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Chapter 2's source-style average is integration against the normalized
domain volume used by `cutoffSpatialLpNorm`. -/
theorem average_eq_integral_domainNormalizedVolume {d : ℕ}
    (U : Ch02.Domain d) (f : Vec d → ℝ) :
    Ch02.average U f = ∫ x, f x ∂domainNormalizedVolume U := by
  unfold Ch02.average domainNormalizedVolume
  let V := U.isDomain.toBoundedMeasurableDomain U.nonempty
  change (volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), f x ∂volume =
    ∫ x, f x ∂V.normalizedVolume
  rw [BoundedMeasurableDomain.normalizedVolume,
    integral_smul_measure, ENNReal.toReal_inv]
  rfl

/-- The absolute normalized average is bounded by every spatial `L^p` norm
with `p >= 1`. -/
theorem ofReal_abs_average_le_cutoffSpatialLpNorm {d : ℕ}
    (U : Ch02.Domain d) (f : Vec d → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f (domainNormalizedVolume U)) :
    ENNReal.ofReal |Ch02.average U f| ≤ cutoffSpatialLpNorm U p f := by
  rw [average_eq_integral_domainNormalizedVolume,
    ← Real.norm_eq_abs, ofReal_norm]
  calc
    ‖∫ x, f x ∂domainNormalizedVolume U‖ₑ ≤
        ∫⁻ x, ‖f x‖ₑ ∂domainNormalizedVolume U :=
      enorm_integral_le_lintegral_enorm f
    _ = eLpNorm f 1 (domainNormalizedVolume U) :=
      (eLpNorm_one_eq_lintegral_enorm hf).symm
    _ ≤ eLpNorm f (ENNReal.ofReal p) (domainNormalizedVolume U) :=
      eLpNorm_le_eLpNorm_of_exponent_le
        (by simpa using ENNReal.ofReal_le_ofReal hp)
    _ = cutoffSpatialLpNorm U p f := (SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf).symm

/-- Measurability of the spatial cutoff norm for a jointly measurable random
field. -/
theorem measurable_cutoffSpatialLpNorm {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (U : Ch02.Domain d)
    (F : Omega → Vec d → ℝ) {p : ℝ} (hp : 0 < p)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun omega ↦ cutoffSpatialLpNorm U p (F omega)) := by
  have hformula : (fun omega ↦ cutoffSpatialLpNorm U p (F omega)) =
      fun omega ↦ (∫⁻ x, ‖F omega x‖ₑ ^ p ∂domainNormalizedVolume U) ^ p⁻¹ := by
    funext omega
    unfold cutoffSpatialLpNorm
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral]
    · rw [ENNReal.toReal_ofReal hp.le, one_div]
    · simpa using hp
    · exact ENNReal.ofReal_ne_top
  rw [hformula]
  exact ENNReal.continuous_rpow_const.measurable.comp
    ((hF.enorm.pow_const p).lintegral_prod_right')

/-- Random suffix average divided by the deterministic prefix diffusivity. -/
noncomputable def oneStepTailCubeRatio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) : Sample d → ℝ :=
  fun omega ↦ tailCoefficientCubeAverage M (n + h) n omega / ahom M n

/-- Reciprocal orientation of `oneStepTailCubeRatio`. -/
noncomputable def oneStepTailCubeInvRatio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) : Sample d → ℝ :=
  fun omega ↦ ahom M n / tailCoefficientCubeAverage M (n + h) n omega

theorem measurable_oneStepTailCubeRatio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) :
    Measurable (oneStepTailCubeRatio M n h) :=
  (measurable_tailCoefficientCubeAverage M (n + h) n).div_const _

theorem measurable_oneStepTailCubeInvRatio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) :
    Measurable (oneStepTailCubeInvRatio M n h) :=
  measurable_const.div (measurable_tailCoefficientCubeAverage M (n + h) n)

theorem oneStepTailCubeRatio_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (omega : Sample d) :
    0 < oneStepTailCubeRatio M n h omega := by
  exact div_pos (tailCoefficientCubeAverage_pos M (n + h) n omega)
    (ahom_pos M n)

theorem oneStepTailCubeInvRatio_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (omega : Sample d) :
    0 < oneStepTailCubeInvRatio M n h omega := by
  exact div_pos (ahom_pos M n)
    (tailCoefficientCubeAverage_pos M (n + h) n omega)

/-- The normalized suffix average is exactly one plus the normalized average
of the cutoff-ratio defect. -/
theorem oneStepTailCubeRatio_eq_one_add_average {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (omega : Sample d) :
    oneStepTailCubeRatio M n h omega =
      1 + Ch02.average (Ch02.cubeDomain (originCube d (n : ℤ)))
        (cutoffRatioMinusOne M (n + h) (n : ℤ) omega) := by
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  have hhom : 0 < ahom M n := ahom_pos M n
  let r : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
      _root_.SubdiffusiveProcess.Model.aCutoff M n omega x
  have hrcont : Continuous r :=
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M (n + h) omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M n omega)
      (fun x ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x).ne')
  have hrint : Integrable r (domainNormalizedVolume U) := by
    let V := U.isDomain.toBoundedMeasurableDomain U.nonempty
    exact V.integrable_normalizedVolume r
      (hrcont.continuousOn.integrableOn_compact
        U.isBoundedDomain.isBounded.isCompact_closure |>.mono_set subset_closure)
  unfold oneStepTailCubeRatio tailCoefficientCubeAverage tailCoefficient
    cutoffRatioMinusOne aCutoffAtInt
  simp only [min_eq_left (Nat.le_add_right n h), Int.toNat_natCast]
  change Ch02.average U (fun x ↦ ahom M n * r x) / ahom M n =
    1 + Ch02.average U (fun x ↦ r x - 1)
  rw [average_eq_integral_domainNormalizedVolume,
    average_eq_integral_domainNormalizedVolume,
    integral_const_mul, integral_sub hrint (integrable_const _), integral_const]
  have hmu : (domainNormalizedVolume U).real Set.univ = 1 := by
    rw [measureReal_def]
    simp
  rw [hmu]
  simp only [one_smul]
  field_simp [hhom.ne']
  ring

private theorem inv_integral_le_integral_inv
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] {r : Omega → ℝ}
    (hrm : Measurable r) (hrpos : ∀ x, 0 < r x)
    (hrint : Integrable r mu) (hrinvint : Integrable (fun x ↦ (r x)⁻¹) mu) :
    (∫ x, r x ∂mu)⁻¹ ≤ ∫ x, (r x)⁻¹ ∂mu := by
  let f : Omega → ℝ := fun x ↦ Real.sqrt (r x)
  let g : Omega → ℝ := fun x ↦ Real.sqrt (r x)⁻¹
  have hf2 : MemLp f 2 mu := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.measurable.comp hrm).aestronglyMeasurable).2
    exact hrint.congr (Filter.Eventually.of_forall fun x ↦
      (Real.sq_sqrt (hrpos x).le).symm)
  have hg2 : MemLp g 2 mu := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.measurable.comp hrm.inv).aestronglyMeasurable).2
    exact hrinvint.congr (Filter.Eventually.of_forall fun x ↦
      (Real.sq_sqrt (inv_pos.mpr (hrpos x)).le).symm)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (f := f) (g := g)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x ↦ Real.sqrt_nonneg (r x))
    (Filter.Eventually.of_forall fun x ↦ Real.sqrt_nonneg (r x)⁻¹)
    (by simpa using hf2) (by simpa using hg2)
  have hfg : ∫ x, f x * g x ∂mu = 1 := by
    calc
      _ = ∫ _x, (1 : ℝ) ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [f, g]
        rw [← Real.sqrt_mul (hrpos x).le,
          mul_inv_cancel₀ (hrpos x).ne', Real.sqrt_one]
      _ = 1 := by simp
  have hf : ∫ x, f x ^ (2 : ℝ) ∂mu = ∫ x, r x ∂mu := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [f]
    rw [Real.rpow_two, Real.sq_sqrt (hrpos x).le]
  have hg : ∫ x, g x ^ (2 : ℝ) ∂mu = ∫ x, (r x)⁻¹ ∂mu := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [g]
    rw [Real.rpow_two, Real.sq_sqrt (inv_pos.mpr (hrpos x)).le]
  rw [hfg, hf, hg] at hcs
  have hA0 : 0 ≤ ∫ x, r x ∂mu := integral_nonneg fun x ↦ (hrpos x).le
  have hB0 : 0 ≤ ∫ x, (r x)⁻¹ ∂mu :=
    integral_nonneg fun x ↦ (inv_pos.mpr (hrpos x)).le
  rw [show (∫ x, r x ∂mu) ^ (1 / 2 : ℝ) =
      Real.sqrt (∫ x, r x ∂mu) by rw [← Real.sqrt_eq_rpow],
    show (∫ x, (r x)⁻¹ ∂mu) ^ (1 / 2 : ℝ) =
      Real.sqrt (∫ x, (r x)⁻¹ ∂mu) by rw [← Real.sqrt_eq_rpow]] at hcs
  have hprod : 1 ≤ (∫ x, r x ∂mu) * ∫ x, (r x)⁻¹ ∂mu := by
    have hsquare := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hcs
    simpa [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0] using hsquare
  have hApos : 0 < ∫ x, r x ∂mu := by
    by_contra hnot
    have hzero : ∫ x, r x ∂mu = 0 :=
      le_antisymm (le_of_not_gt hnot) hA0
    rw [hzero, zero_mul] at hprod
    norm_num at hprod
  exact (inv_le_iff_one_le_mul₀' hApos).2 hprod

/-- Reciprocal Jensen for the literal tail cube average. -/
theorem oneStepTailCubeInvRatio_le_average_inverse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (omega : Sample d) :
    oneStepTailCubeInvRatio M n h omega ≤
      Ch02.average (Ch02.cubeDomain (originCube d (n : ℤ)))
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x) := by
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let r : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
      _root_.SubdiffusiveProcess.Model.aCutoff M n omega x
  have hrcont : Continuous r :=
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M (n + h) omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M n omega)
      (fun x ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x).ne')
  have hrpos : ∀ x, 0 < r x := fun x ↦ div_pos
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x)
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x)
  have hrint : Integrable r (domainNormalizedVolume U) := by
    let V := U.isDomain.toBoundedMeasurableDomain U.nonempty
    exact V.integrable_normalizedVolume r
      (hrcont.continuousOn.integrableOn_compact
        U.isBoundedDomain.isBounded.isCompact_closure |>.mono_set subset_closure)
  have hrinvcont : Continuous (fun x ↦ (r x)⁻¹) :=
    hrcont.inv₀ (fun x ↦ (hrpos x).ne')
  have hrinvint : Integrable (fun x ↦ (r x)⁻¹)
      (domainNormalizedVolume U) := by
    let V := U.isDomain.toBoundedMeasurableDomain U.nonempty
    exact V.integrable_normalizedVolume (fun x ↦ (r x)⁻¹)
      (hrinvcont.continuousOn.integrableOn_compact
        U.isBoundedDomain.isBounded.isCompact_closure |>.mono_set subset_closure)
  have hjensen := inv_integral_le_integral_inv (domainNormalizedVolume U)
    hrcont.measurable hrpos hrint hrinvint
  rw [← average_eq_integral_domainNormalizedVolume U r] at hjensen
  rw [← average_eq_integral_domainNormalizedVolume U (fun x ↦ (r x)⁻¹)] at hjensen
  have hratio : oneStepTailCubeInvRatio M n h omega =
      (oneStepTailCubeRatio M n h omega)⁻¹ := by
    unfold oneStepTailCubeInvRatio oneStepTailCubeRatio
    field_simp [ahom_pos M n |>.ne',
      tailCoefficientCubeAverage_pos M (n + h) n omega |>.ne']
  have havg : Ch02.average U r = oneStepTailCubeRatio M n h omega := by
    rw [oneStepTailCubeRatio_eq_one_add_average]
    change Ch02.average U r = 1 + Ch02.average U (fun x ↦ r x - 1)
    rw [average_eq_integral_domainNormalizedVolume,
      average_eq_integral_domainNormalizedVolume,
      integral_sub hrint (integrable_const _), integral_const]
    have hmu : (domainNormalizedVolume U).real Set.univ = 1 := by
      rw [measureReal_def]
      simp
    rw [hmu]
    simp
  rw [hratio, ← havg]
  refine hjensen.trans_eq ?_
  apply congrArg (Ch02.average U)
  funext x
  dsimp only [r]
  field_simp [_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x |>.ne',
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x |>.ne']

/-- Pointwise direct tail-average control by the spatial cutoff norm. -/
theorem ofReal_oneStepTailCubeRatio_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    {p : ℝ} (hp : 1 ≤ p) (omega : Sample d) :
    ENNReal.ofReal (oneStepTailCubeRatio M n h omega) ≤
      1 + cutoffSpatialLpNorm (Ch02.cubeDomain (originCube d (n : ℤ))) p
        (cutoffRatioMinusOne M (n + h) (n : ℤ) omega) := by
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let f := cutoffRatioMinusOne M (n + h) (n : ℤ) omega
  have hfcont : Continuous f := by
    unfold f cutoffRatioMinusOne aCutoffAtInt
    simp only [Int.toNat_natCast]
    exact (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M (n + h) omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M n omega)
      (fun x ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x).ne')
      |>.sub continuous_const
  have hpoint : oneStepTailCubeRatio M n h omega ≤
      1 + |Ch02.average U f| := by
    rw [oneStepTailCubeRatio_eq_one_add_average]
    simpa only [U, f] using
      add_le_add_right (le_abs_self (Ch02.average U f)) (1 : ℝ)
  calc
    ENNReal.ofReal (oneStepTailCubeRatio M n h omega) ≤
        ENNReal.ofReal (1 + |Ch02.average U f|) :=
      ENNReal.ofReal_le_ofReal hpoint
    _ = 1 + ENNReal.ofReal |Ch02.average U f| := by
      rw [ENNReal.ofReal_add (by norm_num) (abs_nonneg _), ENNReal.ofReal_one]
    _ ≤ 1 + cutoffSpatialLpNorm U p f := by
      gcongr
      exact ofReal_abs_average_le_cutoffSpatialLpNorm U f hp
        hfcont.measurable.aestronglyMeasurable

/-- Pointwise reciprocal tail-average control by the inverse spatial cutoff
norm. -/
theorem ofReal_oneStepTailCubeInvRatio_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    {p : ℝ} (hp : 1 ≤ p) (omega : Sample d) :
    ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega) ≤
      1 + cutoffSpatialLpNorm (Ch02.cubeDomain (originCube d (n : ℤ))) p
        (inverseCutoffRatioMinusOne M (n + h) (n : ℤ) omega) := by
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let f := inverseCutoffRatioMinusOne M (n + h) (n : ℤ) omega
  have hfcont : Continuous f := by
    unfold f inverseCutoffRatioMinusOne aCutoffAtInt
    simp only [Int.toNat_natCast]
    exact (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M n omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M (n + h) omega)
      (fun x ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x).ne')
      |>.sub continuous_const
  have hJ := oneStepTailCubeInvRatio_le_average_inverse M n h omega
  have hfinv : (fun x ↦
      _root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x) =
      fun x ↦ f x + 1 := by
    funext x
    unfold f inverseCutoffRatioMinusOne aCutoffAtInt
    rw [ite_eq_right (not_lt_of_ge (Int.natCast_nonneg n))]
    simp only [Int.toNat_natCast]
    ring
  have hpoint : oneStepTailCubeInvRatio M n h omega ≤
      1 + |Ch02.average U f| := by
    calc
      _ ≤ Ch02.average U (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x) := hJ
      _ = 1 + Ch02.average U f := by
        rw [hfinv]
        rw [average_eq_integral_domainNormalizedVolume,
          average_eq_integral_domainNormalizedVolume,
          integral_add (by
            let V := U.isDomain.toBoundedMeasurableDomain U.nonempty
            exact V.integrable_normalizedVolume f
              (hfcont.continuousOn.integrableOn_compact
                U.isBoundedDomain.isBounded.isCompact_closure
                |>.mono_set subset_closure)) (integrable_const _), integral_const]
        have hmu : (domainNormalizedVolume U).real Set.univ = 1 := by
          rw [measureReal_def]
          simp
        rw [hmu]
        simp
        ring
      _ ≤ 1 + |Ch02.average U f| :=
        add_le_add_right (le_abs_self (Ch02.average U f)) (1 : ℝ)
  calc
    ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega) ≤
        ENNReal.ofReal (1 + |Ch02.average U f|) :=
      ENNReal.ofReal_le_ofReal hpoint
    _ = 1 + ENNReal.ofReal |Ch02.average U f| := by
      rw [ENNReal.ofReal_add (by norm_num) (abs_nonneg _), ENNReal.ofReal_one]
    _ ≤ 1 + cutoffSpatialLpNorm U p f := by
      gcongr
      exact ofReal_abs_average_le_cutoffSpatialLpNorm U f hp
        hfcont.measurable.aestronglyMeasurable

/-- Direct tail-average `L^p` moment, with the exact cutoff-moment payload. -/
theorem paperENNRealLpNorm_oneStepTailCubeRatio_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) {p : ℝ}
    (hp : 1 ≤ p) (hh : 0 < h) :
    paperENNRealLpNorm M.P.toMeasure p
        (fun omega ↦ ENNReal.ofReal (oneStepTailCubeRatio M n h omega)) ≤
      1 + ENNReal.ofReal
        (cutoffMomentConst * Real.sqrt p * M.delta * Real.sqrt (h : ℝ) *
          Real.exp (cutoffMomentConst * p * M.delta ^ 2 * (h : ℝ))) := by
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let E : Sample d → ℝ≥0∞ := fun omega ↦
    cutoffSpatialLpNorm U p (cutoffRatioMinusOne M (n + h) (n : ℤ) omega)
  have hE : Measurable E := measurable_cutoffSpatialLpNorm U _
    (zero_lt_one.trans_le hp) (measurable_cutoffRatioMinusOne_uncurry M (n + h) n)
  have hpoint : ∀ omega, ENNReal.ofReal (oneStepTailCubeRatio M n h omega) ≤
      1 + 1 * E omega := by
    intro omega
    simpa only [one_mul, E, U] using
      ofReal_oneStepTailCubeRatio_le M n h hp omega
  have hnorm := paperENNRealLpNorm_le_one_add_const_mul_of_pointwise
    M.P.toMeasure hp 1 hE hpoint
  refine hnorm.trans ?_
  rw [one_mul]
  gcongr
  simpa only [U, Int.cast_natCast, Int.natCast_sub, Int.cast_ofNat,
    Nat.cast_sub (Nat.le_add_right n h), Nat.cast_add, add_sub_cancel_left]
    using cutoffRatio_spatialLp_moment M U (n + h) (n : ℤ) p hp
      (by omega) (by omega)

/-- Reciprocal twin of `paperENNRealLpNorm_oneStepTailCubeRatio_le`. -/
theorem paperENNRealLpNorm_oneStepTailCubeInvRatio_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) {p : ℝ}
    (hp : 1 ≤ p) (hh : 0 < h) :
    paperENNRealLpNorm M.P.toMeasure p
        (fun omega ↦ ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega)) ≤
      1 + ENNReal.ofReal
        (cutoffMomentConst * Real.sqrt p * M.delta * Real.sqrt (h : ℝ) *
          Real.exp (cutoffMomentConst * p * M.delta ^ 2 * (h : ℝ))) := by
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let E : Sample d → ℝ≥0∞ := fun omega ↦
    cutoffSpatialLpNorm U p
      (inverseCutoffRatioMinusOne M (n + h) (n : ℤ) omega)
  have hE : Measurable E := measurable_cutoffSpatialLpNorm U _
    (zero_lt_one.trans_le hp)
    (measurable_inverseCutoffRatioMinusOne_uncurry M (n + h) n)
  have hpoint : ∀ omega,
      ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega) ≤ 1 + 1 * E omega := by
    intro omega
    simpa only [one_mul, E, U] using
      ofReal_oneStepTailCubeInvRatio_le M n h hp omega
  have hnorm := paperENNRealLpNorm_le_one_add_const_mul_of_pointwise
    M.P.toMeasure hp 1 hE hpoint
  refine hnorm.trans ?_
  rw [one_mul]
  gcongr
  simpa only [U, Int.cast_natCast, Int.natCast_sub, Int.cast_ofNat,
    Nat.cast_sub (Nat.le_add_right n h), Nat.cast_add, add_sub_cancel_left]
    using inverseCutoffRatio_spatialLp_moment M U (n + h) (n : ℤ) p hp
      (by omega) (by omega)

/-- Dimension-free constant for the two eighth moments on a block of length
at most `delta⁻¹`. -/
noncomputable def oneStepTailMomentConst : ℝ :=
  1 + cutoffMomentConst * Real.sqrt 8 *
    Real.exp (4 * cutoffMomentConst)

theorem oneStepTailMomentConst_pos : 0 < oneStepTailMomentConst := by
  unfold oneStepTailMomentConst
  have hC := cutoffMomentConst_pos
  positivity

private theorem cutoff_eight_block_bound_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (h : ℕ)
    (hh : 0 < h) (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    cutoffMomentConst * Real.sqrt 8 * M.delta * Real.sqrt (h : ℝ) *
        Real.exp (cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ)) ≤
      cutoffMomentConst * Real.sqrt 8 *
        Real.exp (4 * cutoffMomentConst) := by
  have hd : 0 < M.delta := M.shellPrefix.delta_pos
  have hhR : 0 ≤ (h : ℝ) := by positivity
  have hdh : M.delta * (h : ℝ) ≤ 1 := by
    calc
      M.delta * (h : ℝ) ≤ M.delta * M.delta⁻¹ := by
        exact mul_le_mul_of_nonneg_left hblock hd.le
      _ = 1 := by exact mul_inv_cancel₀ hd.ne'
  have hdsq : M.delta ^ 2 * (h : ℝ) ≤ M.delta := by
    nlinarith
  have hroot : M.delta * Real.sqrt (h : ℝ) ≤ 1 := by
    have hsquare : (M.delta * Real.sqrt (h : ℝ)) ^ 2 ≤ 1 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hhR]
      nlinarith [M.shellPrefix.delta_le_half]
    exact (sq_le_sq₀ (by positivity) (by norm_num)).mp hsquare
  have hexponent : cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ) ≤
      4 * cutoffMomentConst := by
    have hC := cutoffMomentConst_pos.le
    nlinarith [M.shellPrefix.delta_le_half]
  have hexp := Real.exp_le_exp.mpr hexponent
  have hfront : 0 ≤ cutoffMomentConst * Real.sqrt 8 := by
    exact mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg _)
  calc
    cutoffMomentConst * Real.sqrt 8 * M.delta * Real.sqrt (h : ℝ) *
        Real.exp (cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ)) =
      (cutoffMomentConst * Real.sqrt 8) *
        (M.delta * Real.sqrt (h : ℝ)) *
          Real.exp (cutoffMomentConst * 8 * M.delta ^ 2 * (h : ℝ)) := by ring
    _ ≤ (cutoffMomentConst * Real.sqrt 8) * 1 *
        Real.exp (4 * cutoffMomentConst) := by gcongr
    _ = _ := by ring

/-- Uniform direct eighth moment for all admissible one-step block lengths. -/
theorem paperENNRealLpNorm_oneStepTailCubeRatio_eight_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    paperENNRealLpNorm M.P.toMeasure 8
        (fun omega ↦ ENNReal.ofReal (oneStepTailCubeRatio M n h omega)) ≤
      ENNReal.ofReal oneStepTailMomentConst := by
  by_cases hh : h = 0
  · subst h
    have heq : oneStepTailCubeRatio M n 0 = fun _ ↦ 1 := by
      funext omega
      unfold oneStepTailCubeRatio
      rw [Nat.add_zero, tailCoefficientCubeAverage_self]
      field_simp [ahom_pos M n |>.ne']
    rw [heq]
    have hone := paperENNRealLpNorm_one M.P.toMeasure 8
    rw [show (fun omega ↦ ENNReal.ofReal ((fun _ ↦ (1 : ℝ)) omega)) =
        (fun _ ↦ (1 : ℝ≥0∞)) by funext omega; simp]
    rw [hone]
    have hconst : (1 : ℝ) ≤ oneStepTailMomentConst := by
      unfold oneStepTailMomentConst
      have hnonneg : 0 ≤ cutoffMomentConst * Real.sqrt 8 *
          Real.exp (4 * cutoffMomentConst) := by
        exact mul_nonneg
          (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg _))
          (Real.exp_pos _).le
      linarith
    simpa using ENNReal.ofReal_le_ofReal hconst
  · have hraw := paperENNRealLpNorm_oneStepTailCubeRatio_le M n h
      (by norm_num : (1 : ℝ) ≤ 8) (Nat.pos_of_ne_zero hh)
    have hB := cutoff_eight_block_bound_le M h (Nat.pos_of_ne_zero hh) hblock
    refine hraw.trans ?_
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by norm_num)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg _))
              M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg _))
          (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (by
      unfold oneStepTailMomentConst
      linarith)

/-- Uniform reciprocal eighth moment. -/
theorem paperENNRealLpNorm_oneStepTailCubeInvRatio_eight_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    paperENNRealLpNorm M.P.toMeasure 8
        (fun omega ↦ ENNReal.ofReal (oneStepTailCubeInvRatio M n h omega)) ≤
      ENNReal.ofReal oneStepTailMomentConst := by
  by_cases hh : h = 0
  · subst h
    have heq : oneStepTailCubeInvRatio M n 0 = fun _ ↦ 1 := by
      funext omega
      unfold oneStepTailCubeInvRatio
      rw [Nat.add_zero, tailCoefficientCubeAverage_self]
      field_simp [ahom_pos M n |>.ne']
    rw [heq]
    have hone := paperENNRealLpNorm_one M.P.toMeasure 8
    rw [show (fun omega ↦ ENNReal.ofReal ((fun _ ↦ (1 : ℝ)) omega)) =
        (fun _ ↦ (1 : ℝ≥0∞)) by funext omega; simp]
    rw [hone]
    have hconst : (1 : ℝ) ≤ oneStepTailMomentConst := by
      unfold oneStepTailMomentConst
      have hnonneg : 0 ≤ cutoffMomentConst * Real.sqrt 8 *
          Real.exp (4 * cutoffMomentConst) := by
        exact mul_nonneg
          (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg _))
          (Real.exp_pos _).le
      linarith
    simpa using ENNReal.ofReal_le_ofReal hconst
  · have hraw := paperENNRealLpNorm_oneStepTailCubeInvRatio_le M n h
      (by norm_num : (1 : ℝ) ≤ 8) (Nat.pos_of_ne_zero hh)
    have hB := cutoff_eight_block_bound_le M h (Nat.pos_of_ne_zero hh) hblock
    refine hraw.trans ?_
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by norm_num)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg _))
              M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg _))
          (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (by
      unfold oneStepTailMomentConst
      linarith)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
