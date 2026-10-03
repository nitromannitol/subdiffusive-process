module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.AnnealedDualMeanDefect
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

/-!
# Crude response seed bound

This provider combines the deterministic response-energy comparison, the two
finite-cutoff spatial moment bounds at exponent `2 * xi`, and the sealed
reciprocal lower bound for `ahom`.  Its explicit common-constant enlargement
follows the proof organization of
`Algsuperdiff/Section3/Provider/Base/BaseCaseAssembly.lean`.
-/

open MeasureTheory ProbabilityTheory
open Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.Providers.Section3

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

private theorem paperENNRealLpNorm_eq_eLpNorm_toReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞}
    (hX : ∀ omega, X omega ≠ ∞) :
    paperENNRealLpNorm mu p X =
      SubdiffusiveProcess.RawLp.eLpNorm (fun omega => (X omega).toReal) (ENNReal.ofReal p) mu := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d121_paperENNRealLpNorm_eq_eLpNorm_toReal (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X) (hX := hX)

private theorem average_eq_integral_domainNormalizedVolume {d : ℕ}
    (U : Homogenization.Book.Ch02.Domain d) (f : Homogenization.Vec d → ℝ) :
    Homogenization.Book.Ch02.average U f =
      ∫ x, f x ∂domainNormalizedVolume U := by
  unfold Homogenization.Book.Ch02.average domainNormalizedVolume
  let V := U.isDomain.toBoundedMeasurableDomain U.nonempty
  change (volume (U : Set (Homogenization.Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Homogenization.Vec d)), f x ∂volume =
    ∫ x, f x ∂V.normalizedVolume
  rw [Homogenization.BoundedMeasurableDomain.normalizedVolume,
    integral_smul_measure, ENNReal.toReal_inv]
  rfl

private theorem ofReal_average_sq_eq_cutoffSpatialLpNorm_sq {d : ℕ}
    (U : Homogenization.Book.Ch02.Domain d) (f : Homogenization.Vec d → ℝ)
    (hf : Integrable (fun x => f x ^ 2) (domainNormalizedVolume U)) :
    ENNReal.ofReal (Homogenization.Book.Ch02.average U (fun x => f x ^ 2)) =
      cutoffSpatialLpNorm U 2 f ^ (2 : ℕ) := by
  rw [average_eq_integral_domainNormalizedVolume]
  rw [ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall fun x => sq_nonneg (f x))]
  unfold cutoffSpatialLpNorm
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [one_div]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  norm_num
  apply lintegral_congr
  intro x
  rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
  rw [← ENNReal.ofReal_pow (abs_nonneg (f x))]
  congr 1
  exact (sq_abs (f x)).symm

private theorem measurable_cutoffSpatialLpNorm {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (U : Homogenization.Book.Ch02.Domain d)
    (F : Omega → Homogenization.Vec d → ℝ) (p : ℝ) (hp : 0 < p)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun omega => cutoffSpatialLpNorm U p (F omega)) := by
  have hformula : (fun omega => cutoffSpatialLpNorm U p (F omega)) =
      fun omega => (∫⁻ x, ‖F omega x‖ₑ ^ p ∂domainNormalizedVolume U) ^ p⁻¹ := by
    funext omega
    unfold cutoffSpatialLpNorm
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral]
    · rw [ENNReal.toReal_ofReal hp.le, one_div]
    · simpa using! hp
    · exact ENNReal.ofReal_ne_top
  rw [hformula]
  have hinner : Measurable (fun z : Omega × Homogenization.Vec d =>
      ‖F z.1 z.2‖ₑ ^ p) := by
    simpa [Function.uncurry] using! hF.enorm.pow_const p
  have hlin : Measurable (fun omega =>
      ∫⁻ x, ‖F omega x‖ₑ ^ p ∂domainNormalizedVolume U) :=
    hinner.lintegral_prod_right
  exact hlin.pow_const _

private theorem spatial_affine_norm_le {d : ℕ}
    (U : Homogenization.Book.Ch02.Domain d) (f : Homogenization.Vec d → ℝ)
    (hf : AEStronglyMeasurable f (domainNormalizedVolume U))
    (p c b : ℝ) (hp : 2 ≤ p) :
    cutoffSpatialLpNorm U 2 (fun x => c * f x + b) ≤
      ENNReal.ofReal |c| * cutoffSpatialLpNorm U p f + ENNReal.ofReal |b| := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have htwo : (ENNReal.ofReal (2 : ℝ)) ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal hp
  have hconst : eLpNorm (fun _ : Homogenization.Vec d => b)
      (ENNReal.ofReal p) (domainNormalizedVolume U) = ENNReal.ofReal |b| := by
    rw [eLpNorm_const]
    · rw [measure_univ, ENNReal.one_rpow, mul_one,
        ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    · simpa using! hp0
    · exact NeZero.ne _
  calc
    cutoffSpatialLpNorm U 2 (fun x => c * f x + b) =
        eLpNorm (c • f + fun _ => b) (ENNReal.ofReal 2)
          (domainNormalizedVolume U) := by
      have hcfb : AEStronglyMeasurable (fun x => c * f x + b)
          (domainNormalizedVolume U) := by
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using!
          (hf.const_smul c).add aestronglyMeasurable_const
      rw [cutoffSpatialLpNorm, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hcfb]
      congr 1
    _ ≤ eLpNorm (c • f + fun _ => b) (ENNReal.ofReal p)
          (domainNormalizedVolume U) :=
      eLpNorm_le_eLpNorm_of_exponent_le htwo
    _ ≤ eLpNorm (c • f) (ENNReal.ofReal p) (domainNormalizedVolume U) +
          eLpNorm (fun _ : Homogenization.Vec d => b) (ENNReal.ofReal p)
            (domainNormalizedVolume U) :=
      eLpNorm_add_le
        (by simpa using! ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
    _ = ENNReal.ofReal |c| * cutoffSpatialLpNorm U p f + ENNReal.ofReal |b| := by
      rw [eLpNorm_const_smul, hconst, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
      rw [cutoffSpatialLpNorm, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf]

private theorem cutoffSpatialLpNorm_ne_top_of_continuous {d : ℕ}
    (U : Homogenization.Book.Ch02.Domain d) (p : ℝ)
    (f : Homogenization.Vec d → ℝ) (hf : Continuous f) :
    cutoffSpatialLpNorm U p f ≠ ∞ := by
  let K : Set (Homogenization.Vec d) := closure (U : Set (Homogenization.Vec d))
  let C : ℝ := sSup ((fun x => |f x|) '' K)
  have hK : IsCompact K :=
    U.isDomain.isBoundedDomain.isBounded.isCompact_closure
  have hbdd : BddAbove ((fun x => |f x|) '' K) :=
    hK.bddAbove_image hf.abs.continuousOn
  have hmem : ∀ᵐ x ∂domainNormalizedVolume U, x ∈ (U : Set (Homogenization.Vec d)) := by
    unfold domainNormalizedVolume
    exact Measure.ae_smul_measure (ae_restrict_mem U.measurableSet) _
  have hbound : ∀ᵐ x ∂domainNormalizedVolume U, ‖f x‖ ≤ C := by
    filter_upwards [hmem] with x hx
    change |f x| ≤ C
    exact le_csSup hbdd ⟨x, subset_closure hx, rfl⟩
  have hmemlp : MemLp f (ENNReal.ofReal p) (domainNormalizedVolume U) :=
    MemLp.of_bound hf.aestronglyMeasurable C hbound
  exact ne_top_of_le_ne_top hmemlp.eLpNorm_ne_top
    (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded f _ _)

private theorem normalizedDefect_le_cutoffSpatialNorms {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    (U : Homogenization.Book.Ch02.Domain d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (p : ℝ) (hp : 2 ≤ p) (hhom : 0 < ahom M m) :
    normalizedDefect M m U omega ≤
      (ENNReal.ofReal (ahom M m)⁻¹ *
          (cutoffSpatialLpNorm U p (cutoffRatioMinusOne M m (-1) omega) +
            ENNReal.ofReal (1 - ahom M m))) ^ (2 : ℕ) +
        (cutoffSpatialLpNorm U p (inverseCutoffRatioMinusOne M m (-1) omega) +
          ENNReal.ofReal (1 - ahom M m)) ^ (2 : ℕ) := by
  let alpha := ahom M m
  let a : Homogenization.Vec d → ℝ := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega
  let F : Homogenization.Vec d → ℝ := cutoffRatioMinusOne M m (-1) omega
  let G : Homogenization.Vec d → ℝ := inverseCutoffRatioMinusOne M m (-1) omega
  let Nf : Homogenization.Vec d → ℝ := fun x => a x / alpha - 1
  let Ng : Homogenization.Vec d → ℝ := fun x => alpha / a x - 1
  have halpha_pos : 0 < alpha := hhom
  have halpha : alpha ≤ 1 := ahom_le_one M m
  have hs : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha
  have hF : F = fun x => a x - 1 := by
    funext x
    simp [F, a, cutoffRatioMinusOne, aCutoffAtInt]
  have hG : G = fun x => (a x)⁻¹ - 1 := by
    funext x
    simp [G, a, inverseCutoffRatioMinusOne, aCutoffAtInt]
  have ha_cont : Continuous a :=
    SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M m omega
  have hF_cont : Continuous F := by
    rw [hF]
    exact ha_cont.sub continuous_const
  have hG_cont : Continuous G := by
    rw [hG]
    exact ha_cont.inv₀ (fun x =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega x).ne') |>.sub continuous_const
  have hNf_cont : Continuous Nf :=
    (ha_cont.div_const _).sub continuous_const
  have hNg_cont : Continuous Ng :=
    (continuous_const.div ha_cont (fun x =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega x).ne')).sub continuous_const
  have hsquares (f : Homogenization.Vec d → ℝ) (hf : Continuous f) :
      Integrable (fun x => f x ^ 2) (domainNormalizedVolume U) := by
    let V := U.isDomain.toBoundedMeasurableDomain U.nonempty
    apply V.integrable_normalizedVolume
    exact ((hf.pow 2).continuousOn.integrableOn_compact
      U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  have henergy : ENNReal.ofReal (Homogenization.Book.Ch02.average U
      (fun x => Nf x ^ 2 + Ng x ^ 2)) =
      cutoffSpatialLpNorm U 2 Nf ^ (2 : ℕ) +
        cutoffSpatialLpNorm U 2 Ng ^ (2 : ℕ) := by
    rw [average_eq_integral_domainNormalizedVolume,
      integral_add (hsquares Nf hNf_cont) (hsquares Ng hNg_cont),
      ENNReal.ofReal_add]
    · rw [← average_eq_integral_domainNormalizedVolume,
        ofReal_average_sq_eq_cutoffSpatialLpNorm_sq U Nf (hsquares Nf hNf_cont),
        ← average_eq_integral_domainNormalizedVolume,
        ofReal_average_sq_eq_cutoffSpatialLpNorm_sq U Ng (hsquares Ng hNg_cont)]
    · exact integral_nonneg fun x => sq_nonneg (Nf x)
    · exact integral_nonneg fun x => sq_nonneg (Ng x)
  have hNf : cutoffSpatialLpNorm U 2 Nf ≤
      ENNReal.ofReal alpha⁻¹ * cutoffSpatialLpNorm U p F +
        ENNReal.ofReal (alpha⁻¹ * (1 - alpha)) := by
    have heq : Nf = fun x => alpha⁻¹ * F x + alpha⁻¹ * (1 - alpha) := by
      funext x
      rw [hF]
      dsimp [Nf]
      have halpha_ne : alpha ≠ 0 := hhom.ne'
      field_simp [halpha_ne]
      ring
    rw [heq]
    have hinv : 0 ≤ alpha⁻¹ := inv_nonneg.mpr hhom.le
    simpa only [abs_of_nonneg hinv, abs_of_nonneg (mul_nonneg hinv hs)]
      using! spatial_affine_norm_le U F hF_cont.aestronglyMeasurable p
        alpha⁻¹ (alpha⁻¹ * (1 - alpha)) hp
  have hNf' : cutoffSpatialLpNorm U 2 Nf ≤
      ENNReal.ofReal alpha⁻¹ *
        (cutoffSpatialLpNorm U p F + ENNReal.ofReal (1 - alpha)) := by
    calc
      cutoffSpatialLpNorm U 2 Nf ≤ _ := hNf
      _ = ENNReal.ofReal alpha⁻¹ *
          (cutoffSpatialLpNorm U p F + ENNReal.ofReal (1 - alpha)) := by
        rw [mul_add, ← ENNReal.ofReal_mul (inv_nonneg.mpr hhom.le)]
  have hNg : cutoffSpatialLpNorm U 2 Ng ≤
      cutoffSpatialLpNorm U p G + ENNReal.ofReal (1 - alpha) := by
    have heq : Ng = fun x => alpha * G x - (1 - alpha) := by
      funext x
      rw [hG]
      dsimp [Ng]
      field_simp [(SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega x).ne']
      ring
    have hraw := spatial_affine_norm_le U G hG_cont.aestronglyMeasurable p
      alpha (-(1 - alpha)) hp
    have hfirst : cutoffSpatialLpNorm U 2 Ng ≤
        ENNReal.ofReal alpha * cutoffSpatialLpNorm U p G +
          ENNReal.ofReal (1 - alpha) := by
      rw [heq]
      have hs' : 0 ≤ 1 + -alpha := by linarith
      simpa only [sub_eq_add_neg, abs_of_pos halpha_pos, abs_neg,
        abs_of_nonneg hs'] using! hraw
    calc
      cutoffSpatialLpNorm U 2 Ng ≤
          ENNReal.ofReal alpha * cutoffSpatialLpNorm U p G +
            ENNReal.ofReal (1 - alpha) := hfirst
      _ ≤ cutoffSpatialLpNorm U p G + ENNReal.ofReal (1 - alpha) := by
        gcongr
        exact mul_le_of_le_one_left zero_le
          (ENNReal.ofReal_le_one.mpr halpha)
  calc
    normalizedDefect M m U omega ≤
        ENNReal.ofReal (Homogenization.Book.Ch02.average U
          (fun x => Nf x ^ 2 + Ng x ^ 2)) := by
      simpa [Nf, Ng, a, alpha] using!
        normalizedDefect_le_ratio_energy M m U omega hhom
    _ = cutoffSpatialLpNorm U 2 Nf ^ (2 : ℕ) +
        cutoffSpatialLpNorm U 2 Ng ^ (2 : ℕ) := henergy
    _ ≤ (ENNReal.ofReal alpha⁻¹ *
          (cutoffSpatialLpNorm U p F + ENNReal.ofReal (1 - alpha))) ^ (2 : ℕ) +
        (cutoffSpatialLpNorm U p G + ENNReal.ofReal (1 - alpha)) ^ (2 : ℕ) := by
      gcongr
    _ = _ := by rfl

private theorem eLpNorm_sq_shift_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (hX : AEStronglyMeasurable X mu)
    (xi s : ℝ) (hxi : 1 ≤ xi) (hs : 0 ≤ s) :
    eLpNorm (fun omega => (X omega + s) ^ 2) (ENNReal.ofReal xi) mu ≤
      (eLpNorm X (ENNReal.ofReal (2 * xi)) mu + ENNReal.ofReal s) ^ (2 : ℕ) := by
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
  have h2xi : 1 ≤ ENNReal.ofReal (2 * xi) := by
    simpa using! ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * xi by nlinarith)
  have hconst : eLpNorm (fun _ : Omega => s) (ENNReal.ofReal (2 * xi)) mu =
      ENNReal.ofReal s := by
    rw [eLpNorm_const]
    · rw [measure_univ, ENNReal.one_rpow, mul_one,
        ← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg hs]
    · have : 0 < 2 * xi := mul_pos (by norm_num) hxi0
      simpa using! this
    · exact NeZero.ne _
  calc
    eLpNorm (fun omega => (X omega + s) ^ 2) (ENNReal.ofReal xi) mu =
        eLpNorm (fun omega => ‖X omega + s‖ ^ (2 : ℝ))
          (ENNReal.ofReal xi) mu := by
      congr 2
      funext omega
      norm_num [sq_abs]
    _ = eLpNorm (fun omega => X omega + s)
          (ENNReal.ofReal xi * ENNReal.ofReal 2) mu ^ (2 : ℝ) :=
      eLpNorm_norm_rpow (fun omega => X omega + s)
        (by simpa only [Pi.add_apply] using! hX.add aestronglyMeasurable_const) (by norm_num)
    _ = eLpNorm (X + fun _ => s) (ENNReal.ofReal (2 * xi)) mu ^ (2 : ℝ) := by
      congr 2
      · rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ (eLpNorm X (ENNReal.ofReal (2 * xi)) mu +
          eLpNorm (fun _ : Omega => s) (ENNReal.ofReal (2 * xi)) mu) ^ (2 : ℝ) := by
      gcongr
      exact eLpNorm_add_le h2xi
    _ = (eLpNorm X (ENNReal.ofReal (2 * xi)) mu + ENNReal.ofReal s) ^ (2 : ℕ) := by
      rw [hconst]
      norm_num

private noncomputable def crudeJMomentScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (xi : ℝ) : ℝ :=
  cutoffMomentConst * Real.sqrt (2 * xi) * M.delta *
    Real.sqrt (m + 1 : ℝ) *
      Real.exp (cutoffMomentConst * (2 * xi) * M.delta ^ 2 * (m + 1 : ℝ))

private theorem crudeJ_prebound {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (xi : ℝ)
    (U : Homogenization.Book.Ch02.Domain d) (hxi : 1 ≤ xi) :
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefect M m U) ≤
      ENNReal.ofReal (ahom M m)⁻¹ ^ (2 : ℕ) *
          (ENNReal.ofReal (crudeJMomentScale M m xi) +
            ENNReal.ofReal (1 - ahom M m)) ^ (2 : ℕ) +
        (ENNReal.ofReal (crudeJMomentScale M m xi) +
          ENNReal.ofReal (1 - ahom M m)) ^ (2 : ℕ) := by
  let p : ℝ := 2 * xi
  let alpha : ℝ := ahom M m
  let s : ℝ := 1 - alpha
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ := fun omega =>
    cutoffSpatialLpNorm U p (cutoffRatioMinusOne M m (-1) omega)
  let Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ := fun omega =>
    cutoffSpatialLpNorm U p (inverseCutoffRatioMinusOne M m (-1) omega)
  let x : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega => (X omega).toReal
  let y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega => (Y omega).toReal
  let D : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ := normalizedDefect M m U
  let H : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega =>
    alpha⁻¹ ^ 2 * (x omega + s) ^ 2 + (y omega + s) ^ 2
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
  have hp : 2 ≤ p := by dsimp [p]; nlinarith
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hhom : 0 < alpha := by
    exact lt_of_lt_of_le (Real.exp_pos _)
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m)
  have halpha : alpha ≤ 1 := ahom_le_one M m
  have hs : 0 ≤ s := sub_nonneg.mpr halpha
  have hXmeas : Measurable X := by
    exact measurable_cutoffSpatialLpNorm U (cutoffRatioMinusOne M m (-1)) p
      (by positivity) (measurable_cutoffRatioMinusOne_uncurry M m (-1))
  have hYmeas : Measurable Y := by
    exact measurable_cutoffSpatialLpNorm U (inverseCutoffRatioMinusOne M m (-1)) p
      (by positivity) (measurable_inverseCutoffRatioMinusOne_uncurry M m (-1))
  have hXfinite : ∀ omega, X omega ≠ ∞ := by
    intro omega
    apply cutoffSpatialLpNorm_ne_top_of_continuous
    exact ((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M m omega).div
      (continuous_aCutoffAtInt M (-1) omega)
      (fun z => (aCutoffAtInt_pos M (-1) omega z).ne')).sub continuous_const
  have hYfinite : ∀ omega, Y omega ≠ ∞ := by
    intro omega
    apply cutoffSpatialLpNorm_ne_top_of_continuous
    exact ((continuous_aCutoffAtInt M (-1) omega).div
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M m omega)
      (fun z => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega z).ne')).sub
        continuous_const
  have hxmeas : Measurable x := ENNReal.measurable_toReal.comp hXmeas
  have hymeas : Measurable y := ENNReal.measurable_toReal.comp hYmeas
  have hXmoment : eLpNorm x (ENNReal.ofReal p) M.P.toMeasure ≤
      ENNReal.ofReal (crudeJMomentScale M m xi) := by
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hxmeas.aestronglyMeasurable,
      ← paperENNRealLpNorm_eq_eLpNorm_toReal M.P.toMeasure (by positivity) hXfinite]
    simpa [X, p, crudeJMomentScale] using!
      cutoffRatio_spatialLp_moment M U m (-1) p hp1 (by norm_num)
        (by omega)
  have hYmoment : eLpNorm y (ENNReal.ofReal p) M.P.toMeasure ≤
      ENNReal.ofReal (crudeJMomentScale M m xi) := by
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hymeas.aestronglyMeasurable,
      ← paperENNRealLpNorm_eq_eLpNorm_toReal M.P.toMeasure (by positivity) hYfinite]
    simpa [Y, p, crudeJMomentScale] using!
      inverseCutoffRatio_spatialLp_moment M U m (-1) p hp1 (by norm_num)
        (by omega)
  have hdet : ∀ omega, D omega ≤
      (ENNReal.ofReal alpha⁻¹ * (X omega + ENNReal.ofReal s)) ^ (2 : ℕ) +
        (Y omega + ENNReal.ofReal s) ^ (2 : ℕ) := by
    intro omega
    simpa [D, X, Y, p, alpha, s] using!
      normalizedDefect_le_cutoffSpatialNorms M m U omega p hp hhom
  have hDfinite : ∀ omega, D omega ≠ ∞ := by
    intro omega
    have hprod : ENNReal.ofReal alpha⁻¹ *
        (X omega + ENNReal.ofReal s) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hXfinite omega, ENNReal.ofReal_ne_top⟩)
    have hrhs :
        (ENNReal.ofReal alpha⁻¹ * (X omega + ENNReal.ofReal s)) ^ (2 : ℕ) +
          (Y omega + ENNReal.ofReal s) ^ (2 : ℕ) ≠ ∞ := by
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top hprod,
        ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr
          ⟨hYfinite omega, ENNReal.ofReal_ne_top⟩)⟩
    exact ne_top_of_le_ne_top hrhs (hdet omega)
  have hdH : ∀ omega, ‖(D omega).toReal‖ ≤ ‖H omega‖ := by
    intro omega
    have hprod : ENNReal.ofReal alpha⁻¹ *
        (X omega + ENNReal.ofReal s) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hXfinite omega, ENNReal.ofReal_ne_top⟩)
    have hYsum : Y omega + ENNReal.ofReal s ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨hYfinite omega, ENNReal.ofReal_ne_top⟩
    have hrhs :
        (ENNReal.ofReal alpha⁻¹ * (X omega + ENNReal.ofReal s)) ^ (2 : ℕ) +
          (Y omega + ENNReal.ofReal s) ^ (2 : ℕ) ≠ ∞ := by
      exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.pow_ne_top hprod, ENNReal.pow_ne_top hYsum⟩
    have hreal := ENNReal.toReal_mono hrhs (hdet omega)
    have hHnn : 0 ≤ H omega := by
      dsimp [H]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_eq_abs, abs_of_nonneg hHnn]
    have hXreal : ENNReal.ofReal (x omega) = X omega := by
      exact ENNReal.ofReal_toReal (hXfinite omega)
    have hYreal : ENNReal.ofReal (y omega) = Y omega := by
      exact ENNReal.ofReal_toReal (hYfinite omega)
    rw [← hXreal, ← hYreal] at hreal
    have hinv : 0 ≤ alpha⁻¹ := inv_nonneg.mpr hhom.le
    have hx0 : 0 ≤ x omega := ENNReal.toReal_nonneg
    have hy0 : 0 ≤ y omega := ENNReal.toReal_nonneg
    have hprod' : ENNReal.ofReal alpha⁻¹ *
        (ENNReal.ofReal (x omega) + ENNReal.ofReal s) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
    have hYsum' : ENNReal.ofReal (y omega) + ENNReal.ofReal s ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    rw [ENNReal.toReal_add (ENNReal.pow_ne_top hprod')
        (ENNReal.pow_ne_top hYsum'),
      ENNReal.toReal_pow, ENNReal.toReal_mul,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_pow,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hinv, ENNReal.toReal_ofReal hx0,
      ENNReal.toReal_ofReal hy0, ENNReal.toReal_ofReal hs] at hreal
    change (D omega).toReal ≤ H omega
    calc
      (D omega).toReal ≤ (alpha⁻¹ * (x omega + s)) ^ 2 +
          (y omega + s) ^ 2 := hreal
      _ = H omega := by
        dsimp [H]
        ring
  have hHmeas : AEStronglyMeasurable H M.P.toMeasure := by
    exact (((hxmeas.add_const s).pow_const 2).const_mul (alpha⁻¹ ^ 2) |>.add
      ((hymeas.add_const s).pow_const 2)).aestronglyMeasurable
  have hsqX := eLpNorm_sq_shift_le M.P.toMeasure x hxmeas.aestronglyMeasurable
    xi s hxi hs
  have hsqY := eLpNorm_sq_shift_le M.P.toMeasure y hymeas.aestronglyMeasurable
    xi s hxi hs
  have hHnorm : eLpNorm H (ENNReal.ofReal xi) M.P.toMeasure ≤
      ENNReal.ofReal alpha⁻¹ ^ (2 : ℕ) *
          (ENNReal.ofReal (crudeJMomentScale M m xi) + ENNReal.ofReal s) ^ (2 : ℕ) +
        (ENNReal.ofReal (crudeJMomentScale M m xi) + ENNReal.ofReal s) ^ (2 : ℕ) := by
    calc
      eLpNorm H (ENNReal.ofReal xi) M.P.toMeasure ≤
          eLpNorm (fun omega => alpha⁻¹ ^ 2 * (x omega + s) ^ 2)
              (ENNReal.ofReal xi) M.P.toMeasure +
            eLpNorm (fun omega => (y omega + s) ^ 2)
              (ENNReal.ofReal xi) M.P.toMeasure := by
        simpa only [H, Pi.add_apply] using!
          (eLpNorm_add_le (f := fun omega => alpha⁻¹ ^ 2 * (x omega + s) ^ 2)
            (g := fun omega => (y omega + s) ^ 2)
            (by simpa using! ENNReal.ofReal_le_ofReal hxi))
      _ = ENNReal.ofReal (alpha⁻¹ ^ 2) *
            eLpNorm (fun omega => (x omega + s) ^ 2)
              (ENNReal.ofReal xi) M.P.toMeasure +
            eLpNorm (fun omega => (y omega + s) ^ 2)
              (ENNReal.ofReal xi) M.P.toMeasure := by
        rw [show (fun omega => alpha⁻¹ ^ 2 * (x omega + s) ^ 2) =
            (alpha⁻¹ ^ 2) • (fun omega => (x omega + s) ^ 2) by rfl,
          eLpNorm_const_smul, ← ofReal_norm_eq_enorm, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg alpha⁻¹)]
      _ ≤ ENNReal.ofReal (alpha⁻¹ ^ 2) *
            (eLpNorm x (ENNReal.ofReal p) M.P.toMeasure + ENNReal.ofReal s) ^ (2 : ℕ) +
          (eLpNorm y (ENNReal.ofReal p) M.P.toMeasure + ENNReal.ofReal s) ^ (2 : ℕ) := by
        gcongr
      _ ≤ ENNReal.ofReal (alpha⁻¹ ^ 2) *
            (ENNReal.ofReal (crudeJMomentScale M m xi) + ENNReal.ofReal s) ^ (2 : ℕ) +
          (ENNReal.ofReal (crudeJMomentScale M m xi) + ENNReal.ofReal s) ^ (2 : ℕ) := by
        gcongr
      _ = ENNReal.ofReal alpha⁻¹ ^ (2 : ℕ) *
            (ENNReal.ofReal (crudeJMomentScale M m xi) + ENNReal.ofReal s) ^ (2 : ℕ) +
          (ENNReal.ofReal (crudeJMomentScale M m xi) + ENNReal.ofReal s) ^ (2 : ℕ) := by
        rw [ENNReal.ofReal_pow (inv_nonneg.mpr hhom.le)]
  rw [paperENNRealLpNorm_eq_eLpNorm_toReal M.P.toMeasure hxi0 hDfinite]
  exact (SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (Filter.Eventually.of_forall hdH)).trans
    ((SubdiffusiveProcess.RawLp.eLpNorm_le_guarded H _ _).trans (hHnorm.trans_eq (by rfl)))

private noncomputable def crudeJConst : ℝ :=
  16 * (1 + cutoffMomentConst) ^ 2

private theorem crudeJConst_pos : 0 < crudeJConst := by
  unfold crudeJConst
  have hsum : 0 < 1 + cutoffMomentConst := by
    linarith [cutoffMomentConst_pos]
  exact mul_pos (by norm_num) (sq_pos_of_pos hsum)

private theorem crudeJ_real_bound {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (xi : ℝ)
    (hxi : 1 ≤ xi) :
    (ahom M m)⁻¹ ^ 2 *
          (crudeJMomentScale M m xi + (1 - ahom M m)) ^ 2 +
        (crudeJMomentScale M m xi + (1 - ahom M m)) ^ 2 ≤
      crudeJConst * xi * (m + 1 : ℝ) * M.delta ^ 2 *
        Real.exp (crudeJConst * xi * (m + 1 : ℝ) * M.delta ^ 2) := by
  let K := cutoffMomentConst
  let N : ℝ := m + 1
  let r : ℝ := xi * N * M.delta ^ 2
  let t : ℝ := N * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  let B : ℝ := crudeJMomentScale M m xi
  let alpha : ℝ := ahom M m
  let c : ℝ := alpha⁻¹
  let s : ℝ := 1 - alpha
  let C : ℝ := crudeJConst
  have hK : 0 < K := cutoffMomentConst_pos
  have hN : 0 < N := by dsimp [N]; positivity
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hr : 0 < r := by dsimp [r]; positivity
  have htau : 0 < SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := M.G4.tauSq_pos
  have ht : 0 < t := mul_pos hN htau
  have halpha : 0 < alpha := by
    exact lt_of_lt_of_le (Real.exp_pos _)
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m)
  have halpha_one : alpha ≤ 1 := ahom_le_one M m
  have hc : 0 < c := inv_pos.mpr halpha
  have hc_one : 1 ≤ c := (one_le_inv₀ halpha).2 halpha_one
  have hs : 0 ≤ s := sub_nonneg.mpr halpha_one
  have hlog : Real.log 2 / 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have ht_le : t ≤ r := by
    have htau_le := tauSq_le_delta_sq M
    have hxiN : N * M.delta ^ 2 ≤ xi * N * M.delta ^ 2 := by
      nlinarith [sq_nonneg M.delta]
    calc
      t ≤ N * ((Real.log 2 / 2) * M.delta ^ 2) := by
        dsimp [t]
        gcongr
      _ ≤ N * M.delta ^ 2 := by
        have hsq : 0 ≤ M.delta ^ 2 := sq_nonneg _
        have : (Real.log 2 / 2) * M.delta ^ 2 ≤ M.delta ^ 2 := by
          nlinarith
        exact mul_le_mul_of_nonneg_left this hN.le
      _ ≤ r := by simpa [r] using! hxiN
  have hs_le_t : s ≤ t := by
    have hexp := Real.add_one_le_exp (-t)
    have hlower : Real.exp (-t) ≤ alpha := by
      dsimp [t, N, alpha]
      convert SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m using 1
      congr 1
      ring
    linarith
  have hc_le_exp : c ≤ Real.exp t := by
    have hlower : Real.exp (-t) ≤ alpha := by
      dsimp [t, N, alpha]
      convert SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m using 1
      congr 1
      ring
    have hexpneg : 0 < Real.exp (-t) := Real.exp_pos _
    have hinv := (inv_le_inv₀ halpha hexpneg).2 hlower
    dsimp [c]
    calc
      alpha⁻¹ ≤ (Real.exp (-t))⁻¹ := hinv
      _ = Real.exp t := by
        rw [← Real.exp_neg]
        congr 1
        ring
  have hB : 0 ≤ B := by
    dsimp [B, crudeJMomentScale]
    positivity
  have hBsq : B ^ 2 = 2 * K ^ 2 * r * Real.exp (4 * K * r) := by
    have hsqrtXi : Real.sqrt (2 * xi) ^ 2 = 2 * xi :=
      Real.sq_sqrt (by positivity)
    have hsqrtN : Real.sqrt (m + 1 : ℝ) ^ 2 = (m + 1 : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hexpSq :
        Real.exp (cutoffMomentConst * (2 * xi) * M.delta ^ 2 *
            (m + 1 : ℝ)) ^ 2 =
          Real.exp (4 * cutoffMomentConst *
            (xi * (m + 1 : ℝ) * M.delta ^ 2)) := by
      rw [← Real.exp_nat_mul]
      apply congrArg Real.exp
      push_cast
      ring
    dsimp [B, crudeJMomentScale, K, r, N]
    calc
      (cutoffMomentConst * Real.sqrt (2 * xi) * M.delta *
          Real.sqrt (m + 1 : ℝ) *
          Real.exp (cutoffMomentConst * (2 * xi) * M.delta ^ 2 *
            (m + 1 : ℝ))) ^ 2 =
          cutoffMomentConst ^ 2 * Real.sqrt (2 * xi) ^ 2 * M.delta ^ 2 *
            Real.sqrt (m + 1 : ℝ) ^ 2 *
              Real.exp (cutoffMomentConst * (2 * xi) * M.delta ^ 2 *
                (m + 1 : ℝ)) ^ 2 := by ring
      _ = _ := by
        rw [hsqrtXi, hsqrtN, hexpSq]
        ring
  have hr_le_exp : r ≤ Real.exp r := by
    calc
      r ≤ r + 1 := by norm_num
      _ ≤ Real.exp r := Real.add_one_le_exp r
  have hCcoeff : 8 * K ^ 2 + 4 ≤ C := by
    dsimp [C, crudeJConst]
    nlinarith [sq_nonneg K]
  have hCrate : 4 * K + 2 ≤ C := by
    dsimp [C, crudeJConst]
    nlinarith [sq_nonneg K]
  have hCthree : 3 ≤ C := by
    dsimp [C, crudeJConst]
    nlinarith [sq_nonneg K]
  have hexpKt : Real.exp ((4 * K + 2) * r) ≤ Real.exp (C * r) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hCrate hr.le
  have hexpThree : Real.exp (3 * r) ≤ Real.exp (C * r) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hCthree hr.le
  have hmain : c ^ 2 * (B + s) ^ 2 + (B + s) ^ 2 ≤
      C * r * Real.exp (C * r) := by
    calc
      c ^ 2 * (B + s) ^ 2 + (B + s) ^ 2 ≤
          2 * c ^ 2 * (B + s) ^ 2 := by
        have hc2one : 1 ≤ c ^ 2 := one_le_pow₀ hc_one
        nlinarith [sq_nonneg (B + s)]
      _ ≤ 2 * Real.exp (2 * t) * (B + s) ^ 2 := by
        have hc2 : c ^ 2 ≤ Real.exp (2 * t) := by
          calc
            c ^ 2 ≤ (Real.exp t) ^ 2 := by gcongr
            _ = Real.exp (2 * t) := by rw [← Real.exp_nat_mul]; norm_num
        gcongr
      _ ≤ 4 * Real.exp (2 * t) * (B ^ 2 + s ^ 2) := by
        have hsum : (B + s) ^ 2 ≤ 2 * (B ^ 2 + s ^ 2) := by nlinarith [sq_nonneg (B - s)]
        calc
          2 * Real.exp (2 * t) * (B + s) ^ 2 ≤
              2 * Real.exp (2 * t) * (2 * (B ^ 2 + s ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hsum
              (mul_nonneg (by norm_num) (Real.exp_pos _).le)
          _ = 4 * Real.exp (2 * t) * (B ^ 2 + s ^ 2) := by ring
      _ ≤ 4 * Real.exp (2 * r) * (B ^ 2 + r ^ 2) := by
        have hexp : Real.exp (2 * t) ≤ Real.exp (2 * r) := by gcongr
        have hs2 : s ^ 2 ≤ r ^ 2 := by
          have hsr : s ≤ r := hs_le_t.trans ht_le
          nlinarith
        gcongr
      _ = 8 * K ^ 2 * r * Real.exp ((4 * K + 2) * r) +
          4 * r ^ 2 * Real.exp (2 * r) := by
        rw [hBsq, show (4 * K + 2) * r = 2 * r + 4 * K * r by ring,
          Real.exp_add]
        ring
      _ ≤ 8 * K ^ 2 * r * Real.exp (C * r) +
          4 * r * Real.exp (3 * r) := by
        have hr2 : r ^ 2 * Real.exp (2 * r) ≤ r * Real.exp (3 * r) := by
          have hrr : r ^ 2 ≤ r * Real.exp r := by
            calc
              r ^ 2 = r * r := by ring
              _ ≤ r * Real.exp r := mul_le_mul_of_nonneg_left hr_le_exp hr.le
          calc
            r ^ 2 * Real.exp (2 * r) ≤ r * Real.exp r * Real.exp (2 * r) :=
              mul_le_mul_of_nonneg_right hrr (Real.exp_pos _).le
            _ = r * Real.exp (3 * r) := by
              rw [show 3 * r = r + 2 * r by ring, Real.exp_add]
              ring
        exact add_le_add
          (mul_le_mul_of_nonneg_left hexpKt
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg K)) hr.le))
          (by simpa [mul_assoc] using!
            mul_le_mul_of_nonneg_left hr2 (by norm_num : (0 : ℝ) ≤ 4))
      _ ≤ (8 * K ^ 2 + 4) * r * Real.exp (C * r) := by
        calc
          8 * K ^ 2 * r * Real.exp (C * r) + 4 * r * Real.exp (3 * r) ≤
              8 * K ^ 2 * r * Real.exp (C * r) +
                4 * r * Real.exp (C * r) := by
            exact add_le_add (le_refl _)
              (by
                have hmul := mul_le_mul_of_nonneg_left hexpThree
                  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hr.le)
                simpa [mul_assoc] using! hmul)
          _ = (8 * K ^ 2 + 4) * r * Real.exp (C * r) := by ring
      _ ≤ C * r * Real.exp (C * r) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCcoeff hr.le) (Real.exp_pos _).le
  have htarget :
      crudeJConst * xi * (m + 1 : ℝ) * M.delta ^ 2 *
          Real.exp (crudeJConst * xi * (m + 1 : ℝ) * M.delta ^ 2) =
        C * r * Real.exp (C * r) := by
    dsimp [C, r, N]
    congr 1 <;> ring_nf
  rw [htarget]
  simpa only [B, c, s] using! hmain

theorem crude_j_bound {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (xi : ℝ)
        (U : Ch02.Domain d),
        1 ≤ xi →
        (U : Set (Vec d)) ⊆
          Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)) →
        paperENNRealLpNorm M.P.toMeasure xi (normalizedDefect M m U) ≤
          ENNReal.ofReal
            (C * xi * (m + 1 : ℝ) * M.delta ^ 2 *
              Real.exp (C * xi * (m + 1 : ℝ) * M.delta ^ 2)) := by
  by_cases hd : d = 0
  · subst d
    refine ⟨crudeJConst, crudeJConst_pos, ?_⟩
    intro M m xi U _hxi _hU
    letI : IsEmpty {e : Homogenization.Vec 0 // Homogenization.vecNormSq e = 1} :=
      ⟨fun e => by
        have he := e.property
        simp [Homogenization.vecNormSq, Homogenization.vecDot] at he⟩
    have hdef : normalizedDefect M m U = fun _ => 0 := by
      funext omega
      rw [normalizedDefect, paperScalarProbeMaxOn, iSup_of_empty]
      exact ENNReal.bot_eq_zero
    rw [hdef]
    have hxi0 : 0 < xi := zero_lt_one.trans_le _hxi
    simp [paperENNRealLpNorm, ENNReal.zero_rpow_of_pos hxi0,
      ENNReal.zero_rpow_of_pos (inv_pos.mpr hxi0)]
  letI : NeZero d := ⟨hd⟩
  refine ⟨crudeJConst, crudeJConst_pos, ?_⟩
  intro M m xi U hxi _hU
  let B := crudeJMomentScale M m xi
  let alpha := ahom M m
  let s := 1 - alpha
  have halpha : 0 < alpha := by
    exact lt_of_lt_of_le (Real.exp_pos _)
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m)
  have hs : 0 ≤ s := sub_nonneg.mpr (ahom_le_one M m)
  have hB : 0 ≤ B := by
    have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
    have hdelta0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
    dsimp [B, crudeJMomentScale]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg _)) hdelta0)
        (Real.sqrt_nonneg _))
      (Real.exp_pos _).le
  calc
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefect M m U) ≤
        ENNReal.ofReal alpha⁻¹ ^ (2 : ℕ) *
            (ENNReal.ofReal B + ENNReal.ofReal s) ^ (2 : ℕ) +
          (ENNReal.ofReal B + ENNReal.ofReal s) ^ (2 : ℕ) := by
      simpa [B, alpha, s] using! crudeJ_prebound M m xi U hxi
    _ = ENNReal.ofReal
          (alpha⁻¹ ^ 2 * (B + s) ^ 2 + (B + s) ^ 2) := by
      rw [← ENNReal.ofReal_pow (inv_nonneg.mpr halpha.le),
        ← ENNReal.ofReal_add hB hs, ← ENNReal.ofReal_pow (add_nonneg hB hs),
        ← ENNReal.ofReal_mul (sq_nonneg alpha⁻¹),
        ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg alpha⁻¹) (sq_nonneg (B + s)))
          (sq_nonneg (B + s))]
    _ ≤ ENNReal.ofReal
          (crudeJConst * xi * (m + 1 : ℝ) * M.delta ^ 2 *
            Real.exp (crudeJConst * xi * (m + 1 : ℝ) * M.delta ^ 2)) :=
      ENNReal.ofReal_le_ofReal (by
        simpa [B, alpha, s] using! crudeJ_real_bound M m xi hxi)

end

end SubdiffusiveProcess.Providers.Section3
