
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.FractionalHolderBridge

@[expose] public section

/-!
# Fractional Poincare at the Section 6 carrier

This file proves the Jensen--kernel form of fractional Poincare directly for
the paper's `fractionalSeminormOn`.  The latter contains a factor `sqrt s`, so
the resulting estimate has the printed `s^(-1/2)` loss.

The measure normalization uses the Euclidean `fractionalKernel` and the `sqrt s` factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

noncomputable def poincareNormalizedVolume (W : Set (Vec d)) :
    Measure (Vec d) :=
  (volume W)⁻¹ • volume.restrict W

private theorem isProbabilityMeasure_poincareNormalizedVolume
    {W : Set (Vec d)} (hWpos : 0 < volume W) (hWtop : volume W ≠ ∞) :
    IsProbabilityMeasure (poincareNormalizedVolume W) := by
  refine ⟨?_⟩
  rw [poincareNormalizedVolume, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hWpos.ne' hWtop

private theorem eLpNorm_two_eq_rpow {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E : Type*} [NormedAddCommGroup E] (f : α → E) :
    SubdiffusiveProcess.RawLp.eLpNorm f 2 μ =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num)]
  norm_num

private theorem guarded_eLpNorm_two_eq_rpow {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E : Type*} [NormedAddCommGroup E] (f : α → E) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num

private theorem enorm_sub_integral_rpow_two_le
    {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → E} (hf : Integrable f μ) (x : α) :
    ‖f x - ∫ y, f y ∂μ‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂μ := by
  have hgm : AEStronglyMeasurable (fun y => f x - f y) μ :=
    aestronglyMeasurable_const.sub hf.aestronglyMeasurable
  have hint : ∫ y, (f x - f y) ∂μ = f x - ∫ y, f y ∂μ := by
    rw [integral_sub (integrable_const _) hf, integral_const]
    simp
  have h1 : ‖f x - ∫ y, f y ∂μ‖ₑ ≤ ∫⁻ y, ‖f x - f y‖ₑ ∂μ := by
    rw [← hint]
    exact enorm_integral_le_lintegral_enorm _
  have h2 : (∫⁻ y, ‖f x - f y‖ₑ ∂μ) ≤
      (∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have hcmp := eLpNorm_le_eLpNorm_of_exponent_le (μ := μ) (p := 1) (q := 2)
      (f := fun y => f x - f y) (by norm_num)
    rwa [eLpNorm_one_eq_lintegral_enorm hgm, guarded_eLpNorm_two_eq_rpow _ hgm] at hcmp
  have h4 : ‖f x - ∫ y, f y ∂μ‖ₑ ^ (2 : ℝ) ≤
      ((∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num)
  refine h4.trans (le_of_eq ?_)
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem eLpNorm_sub_integral_le_eLpNorm_prod
    {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → E} (hf : Integrable f μ) :
    eLpNorm (fun x => f x - ∫ y, f y ∂μ) 2 μ ≤
      eLpNorm (fun z : α × α => f z.1 - f z.2) 2 (μ.prod μ) := by
  have hfm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  rw [guarded_eLpNorm_two_eq_rpow _ (by simpa only [Pi.sub_apply] using! hfm.sub aestronglyMeasurable_const),
    guarded_eLpNorm_two_eq_rpow _ (by simpa only [Pi.sub_apply] using! hfm.comp_fst.sub hfm.comp_snd)]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hmeas : AEMeasurable
      (fun z : α × α => ‖f z.1 - f z.2‖ₑ ^ (2 : ℝ)) (μ.prod μ) :=
    ((hfm.comp_fst.sub hfm.comp_snd).enorm).pow_const _
  rw [lintegral_prod _ hmeas]
  exact lintegral_mono fun x => enorm_sub_integral_rpow_two_le μ hf x

private theorem euclideanNorm_sub_le_rpow_mul_fractionalKernel
    {s D : ℝ} (hs : 0 ≤ s) (f : Vec d → Vec d) {x y : Vec d}
    (hxy : euclideanNorm (x - y) ≤ D) :
    euclideanNorm (f x - f y) ≤
      D ^ (s + (d : ℝ) / 2) * fractionalKernel s f (x, y) := by
  let r := euclideanNorm (x - y)
  let e := s + (d : ℝ) / 2
  have he0 : 0 ≤ e := by
    dsimp [e]
    positivity
  have hr0 : 0 ≤ r := euclideanNorm_nonneg _
  have hD0 : 0 ≤ D := hr0.trans hxy
  rcases eq_or_lt_of_le hr0 with hrzero | hrpos
  · have hxyzero : x = y := by
      apply sub_eq_zero.mp
      exact euclideanNorm_eq_zero_iff.mp hrzero.symm
    simp [hxyzero, fractionalKernel]
  · have hmono : r ^ e ≤ D ^ e := Real.rpow_le_rpow hr0 hxy he0
    have hcancel : r ^ e * r ^ (-e) = 1 := by
      rw [← Real.rpow_add hrpos, add_neg_cancel, Real.rpow_zero]
    have hkernel : fractionalKernel s f (x, y) =
        r ^ (-e) * euclideanNorm (f x - f y) := by
      unfold fractionalKernel
      rw [div_eq_mul_inv, ← Real.rpow_neg hr0]
      dsimp [r, e]
      ring
    rw [hkernel, ← mul_assoc]
    calc
      euclideanNorm (f x - f y) =
          r ^ e * r ^ (-e) * euclideanNorm (f x - f y) := by rw [hcancel, one_mul]
      _ ≤ D ^ e * r ^ (-e) * euclideanNorm (f x - f y) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hr0 _))
          (euclideanNorm_nonneg _)

private theorem raw_two_smul_measure {α ε : Type*} [MeasurableSpace α] [ENorm ε]
    (f : α → ε) (c : ℝ≥0∞) (μ : Measure α) :
    SubdiffusiveProcess.RawLp.eLpNorm f 2 (c • μ) = c ^ (1 / 2 : ℝ) * SubdiffusiveProcess.RawLp.eLpNorm f 2 μ := by
  norm_num only [SubdiffusiveProcess.RawLp.eLpNorm, ENNReal.toReal_ofNat]
  exact eLpNorm'_smul_measure (by norm_num) c

private theorem raw_two_const_smul {α : Type*} [MeasurableSpace α]
    (f : α → ℝ) (c : ℝ) (μ : Measure α) :
    SubdiffusiveProcess.RawLp.eLpNorm (c • f) 2 μ = ‖c‖ₑ * SubdiffusiveProcess.RawLp.eLpNorm f 2 μ := by
  norm_num only [SubdiffusiveProcess.RawLp.eLpNorm, ENNReal.toReal_ofNat]
  exact eLpNorm'_const_smul c (by norm_num)

private theorem raw_two_mono_ae {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {μ : Measure α}
    {f : α → E} {g : α → F} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    SubdiffusiveProcess.RawLp.eLpNorm f 2 μ ≤ SubdiffusiveProcess.RawLp.eLpNorm g 2 μ := by
  norm_num only [SubdiffusiveProcess.RawLp.eLpNorm, ENNReal.toReal_ofNat]
  exact eLpNorm'_mono_ae (by norm_num) h

/-- Jensen and the fractional kernel on an arbitrary positive finite-volume
window.  This is the extended-real form used before taking the
`sqrt(s)` normalization into account. -/
theorem eLpNorm_hilbertVec_sub_mean_le_fractionalKernel
    {W : Set (Vec d)} {s D : ℝ} {f : Vec d → Vec d}
    (hW : MeasurableSet W) (hWpos : 0 < volume W) (hWtop : volume W ≠ ∞)
    (hs : 0 ≤ s)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, euclideanNorm (x - y) ≤ D)
    (hf : Integrable (fun x => HilbertVec.ofVec (f x))
      (volume.restrict W)) :
    eLpNorm
        (fun x => HilbertVec.ofVec (f x) -
          ∫ y, HilbertVec.ofVec (f y) ∂(poincareNormalizedVolume W))
        2 (poincareNormalizedVolume W) ≤
      ENNReal.ofReal (D ^ (s + (d : ℝ) / 2)) *
        SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2
          ((poincareNormalizedVolume W).prod (poincareNormalizedVolume W)) := by
  classical
  let μ := poincareNormalizedVolume W
  have := isProbabilityMeasure_poincareNormalizedVolume hWpos hWtop
  have hfμ : Integrable (fun x => HilbertVec.ofVec (f x)) μ := by
    dsimp [μ, poincareNormalizedVolume]
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr hWpos.ne')
  have haeW : ∀ᵐ x ∂μ, x ∈ W := by
    dsimp [μ, poincareNormalizedVolume]
    exact Measure.ae_smul_measure (ae_restrict_mem hW) _
  have hae1 : ∀ᵐ z ∂(μ.prod μ), z.1 ∈ W :=
    Measure.quasiMeasurePreserving_fst.ae haeW
  have hae2 : ∀ᵐ z ∂(μ.prod μ), z.2 ∈ W :=
    Measure.quasiMeasurePreserving_snd.ae haeW
  have hkernel : eLpNorm
      (fun z : Vec d × Vec d =>
        HilbertVec.ofVec (f z.1) - HilbertVec.ofVec (f z.2)) 2 (μ.prod μ) ≤
      ENNReal.ofReal (D ^ (s + (d : ℝ) / 2)) *
        SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2 (μ.prod μ) := by
    have hmono : eLpNorm
        (fun z : Vec d × Vec d =>
          HilbertVec.ofVec (f z.1) - HilbertVec.ofVec (f z.2)) 2 (μ.prod μ) ≤
        SubdiffusiveProcess.RawLp.eLpNorm ((D ^ (s + (d : ℝ) / 2)) • fractionalKernel s f) 2
          (μ.prod μ) := by
      have hdiffMeas : AEStronglyMeasurable
          (fun z : Vec d × Vec d => HilbertVec.ofVec (f z.1) - HilbertVec.ofVec (f z.2))
          (μ.prod μ) := by
        simpa only [Pi.sub_apply] using! hfμ.aestronglyMeasurable.comp_fst.sub hfμ.aestronglyMeasurable.comp_snd
      rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hdiffMeas]
      refine raw_two_mono_ae ?_
      filter_upwards [hae1, hae2] with z hz1 hz2
      have hb := euclideanNorm_sub_le_rpow_mul_fractionalKernel hs f
        (hdiam z.1 hz1 z.2 hz2)
      have hDpow : 0 ≤ D ^ (s + (d : ℝ) / 2) :=
        Real.rpow_nonneg (by
          have := euclideanNorm_nonneg (z.1 - z.2)
          exact this.trans (hdiam z.1 hz1 z.2 hz2)) _
      have hfrac : 0 ≤ fractionalKernel s f z := by
        unfold fractionalKernel
        exact div_nonneg (euclideanNorm_nonneg _)
          (Real.rpow_nonneg (euclideanNorm_nonneg _) _)
      have hnorm :
          ‖HilbertVec.ofVec (f z.1) - HilbertVec.ofVec (f z.2)‖ =
            euclideanNorm (f z.1 - f z.2) := by
        change ‖(HilbertVec.ofVecL d) (f z.1) -
          (HilbertVec.ofVecL d) (f z.2)‖ = _
        rw [← (HilbertVec.ofVecL d).map_sub]
        exact (euclideanNorm_eq_norm_ofVec _).symm
      rw [hnorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hDpow, Real.norm_eq_abs, abs_of_nonneg hfrac]
      exact hb
    refine hmono.trans (le_of_eq ?_)
    have hD0 : 0 ≤ D := by
      obtain ⟨x, hx⟩ : W.Nonempty := nonempty_of_measure_ne_zero hWpos.ne'
      exact (euclideanNorm_nonneg (x - x)).trans (hdiam x hx x hx)
    rw [raw_two_const_smul,
      Real.enorm_eq_ofReal (Real.rpow_nonneg hD0 _)]
  exact (eLpNorm_sub_integral_le_eLpNorm_prod μ hfμ).trans hkernel

private theorem integral_hilbertVec_poincareNormalizedVolume_eq_averageVecOn
    {W : Set (Vec d)} {f : Vec d → Vec d}
    (hf : Integrable (fun x => HilbertVec.ofVec (f x)) (volume.restrict W)) :
    (∫ y, HilbertVec.ofVec (f y) ∂(poincareNormalizedVolume W)) =
      HilbertVec.ofVec (averageVecOn W f) := by
  rw [poincareNormalizedVolume, integral_smul_measure]
  apply (HilbertVec.continuousLinearEquivVec d).injective
  rw [(HilbertVec.continuousLinearEquivVec d).map_smul]
  rw [← (HilbertVec.continuousLinearEquivVec d).integral_comp_comm
    (fun x => HilbertVec.ofVec (f x))]
  simp only [HilbertVec.continuousLinearEquivVec_apply, HilbertVec.toVec_ofVec]
  have hfvec : Integrable f (volume.restrict W) := by
    simpa only [HilbertVec.continuousLinearEquivVec_apply, HilbertVec.toVec_ofVec] using!
      (HilbertVec.continuousLinearEquivVec d : HilbertVec d →L[ℝ] Vec d).integrable_comp hf
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hi := (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).integral_comp_comm hfvec
  have hicoord : (∫ x in W, f x ∂volume) i = ∫ x in W, f x i ∂volume := hi.symm
  rw [hicoord]
  change (volume W)⁻¹.toReal * (∫ x in W, f x i) = _
  simp only [averageVecOn, volumeAverage, ENNReal.toReal_inv]

private theorem eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq
    {W : Set (Vec d)} {f : Vec d → Vec d}
    (hWpos : 0 < (volume W).toReal)
    (hf : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W)) :
    (eLpNorm (fun x => HilbertVec.ofVec (f x)) 2
      (poincareNormalizedVolume W)).toReal =
        vectorNormalizedL2On W f := by
  have hVtop : volume W ≠ ∞ := (ENNReal.toReal_ne_zero.mp hWpos.ne').2
  have hVzero : volume W ≠ 0 := by
    exact (ENNReal.toReal_ne_zero.mp hWpos.ne').1
  have hnorm : MemLp (fun x => euclideanNorm (f x)) 2 (volume.restrict W) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using! hf.norm
  rw [poincareNormalizedVolume,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) _ _ hf.aestronglyMeasurable]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_mul]
  norm_num
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_inv]
  rw [← eLpNorm_norm _ hf.aestronglyMeasurable]
  rw [show (fun x => ‖HilbertVec.ofVec (f x)‖) =
      (fun x => euclideanNorm (f x)) by
    funext x
    exact (euclideanNorm_eq_norm_ofVec _).symm]
  change _ = normalizedL2On W (fun x => euclideanNorm (f x))
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div
    hnorm]
  rw [Real.sqrt_eq_rpow]
  have hV : 0 < (volume W).toReal := hWpos
  rw [Real.inv_rpow hV.le]
  ring

private theorem fractionalKernel_poincareNormalizedVolume_prod_toReal_eq
    {W : Set (Vec d)} {s : ℝ} {f : Vec d → Vec d}
    (hWpos : 0 < (volume W).toReal) (hs : 0 < s) :
    (SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2
      ((poincareNormalizedVolume W).prod
        (poincareNormalizedVolume W))).toReal =
      s ^ (-(1 / 2 : ℝ)) * (volume W).toReal ^ (-(1 / 2 : ℝ)) *
        (fractionalSeminormOn W s f).toReal := by
  let R := (SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2
    ((volume.restrict W).prod (volume.restrict W))).toReal
  have hmeasure :
      (poincareNormalizedVolume W).prod (poincareNormalizedVolume W) =
        ((volume W)⁻¹ * (volume W)⁻¹) •
          ((volume.restrict W).prod (volume.restrict W)) := by
    rw [poincareNormalizedVolume, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul]
  have hleft :
      (SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2
        ((poincareNormalizedVolume W).prod
          (poincareNormalizedVolume W))).toReal =
        (volume W).toReal⁻¹ * R := by
    rw [hmeasure,
      raw_two_smul_measure]
    simp only [ENNReal.toReal_mul]
    norm_num
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hV : 0 < (volume W).toReal := hWpos
    rw [Real.mul_rpow (by positivity : 0 ≤ (volume W).toReal⁻¹)
      (by positivity : 0 ≤ (volume W).toReal⁻¹),
      Real.inv_rpow hV.le, ← mul_inv, ← Real.rpow_add hV]
    norm_num
    left
    rfl
  have hright :
      (fractionalSeminormOn W s f).toReal =
        s ^ (1 / 2 : ℝ) * (volume W).toReal ^ (-(1 / 2 : ℝ)) * R := by
    unfold fractionalSeminormOn
    simp only [ENNReal.toReal_mul]
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_div, ENNReal.toReal_ofReal hs.le]
    rw [Real.div_rpow hs.le hWpos.le, div_eq_mul_inv,
      ← Real.rpow_neg hWpos.le]
  rw [hleft, hright]
  have hsroot : s ^ (-(1 / 2 : ℝ)) * s ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hs]
    norm_num
  have hVroot : (volume W).toReal ^ (-(1 / 2 : ℝ)) *
      (volume W).toReal ^ (-(1 / 2 : ℝ)) = (volume W).toReal⁻¹ := by
    rw [← Real.rpow_add hWpos]
    norm_num
    exact Real.rpow_neg_one _
  calc
    (volume W).toReal⁻¹ * R =
        1 * (volume W).toReal⁻¹ * R := by ring
    _ = (s ^ (-(1 / 2 : ℝ)) * s ^ (1 / 2 : ℝ)) *
        ((volume W).toReal ^ (-(1 / 2 : ℝ)) *
          (volume W).toReal ^ (-(1 / 2 : ℝ))) * R := by
      rw [hsroot, hVroot]
    _ = s ^ (-(1 / 2 : ℝ)) * (volume W).toReal ^ (-(1 / 2 : ℝ)) *
        (s ^ (1 / 2 : ℝ) * (volume W).toReal ^ (-(1 / 2 : ℝ)) * R) := by
      ring

private theorem eLpNorm_fractionalKernel_poincareNormalizedVolume_ne_top
    {W : Set (Vec d)} {s : ℝ} {f : Vec d → Vec d}
    (hWpos : 0 < volume W) (hWtop : volume W ≠ ∞) (hs : 0 < s)
    (hfrac : fractionalSeminormOn W s f ≠ ∞) :
    SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2
      ((poincareNormalizedVolume W).prod
        (poincareNormalizedVolume W)) ≠ ∞ := by
  have hpref0 : (ENNReal.ofReal s / volume W) ^ (1 / 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos
      (ENNReal.div_pos (ENNReal.ofReal_ne_zero_iff.mpr hs) hWtop)
      (ENNReal.div_ne_top ENNReal.ofReal_ne_top hWpos.ne'))
  have hraw : SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2
      ((volume.restrict W).prod (volume.restrict W)) ≠ ∞ := by
    intro htop
    apply hfrac
    unfold fractionalSeminormOn
    rw [htop, ENNReal.mul_top hpref0]
  have hmeasure :
      (poincareNormalizedVolume W).prod (poincareNormalizedVolume W) =
        ((volume W)⁻¹ * (volume W)⁻¹) •
          ((volume.restrict W).prod (volume.restrict W)) := by
    rw [poincareNormalizedVolume, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul]
  rw [hmeasure,
    raw_two_smul_measure]
  exact ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hWpos.ne')
        (ENNReal.inv_ne_top.mpr hWpos.ne')))
    hraw

/-- Mean-zero fractional Poincare in the exact real-valued Section 6
carriers.  The constant is the diameter factor and the normalization
contributes exactly `s^(-1/2) |W|^(-1/2)`. -/
theorem vectorNormalizedL2On_sub_averageVecOn_le_fractionalSeminormOn
    {W : Set (Vec d)} {s D : ℝ} {f : Vec d → Vec d}
    (hW : MeasurableSet W) (hWpos : 0 < volume W) (hWtop : volume W ≠ ∞)
    (hs : 0 < s)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, euclideanNorm (x - y) ≤ D)
    (hf : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W))
    (hfrac : fractionalSeminormOn W s f ≠ ∞) :
    vectorNormalizedL2On W (fun x => f x - averageVecOn W f) ≤
      D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
        (volume W).toReal ^ (-(1 / 2 : ℝ)) *
          (fractionalSeminormOn W s f).toReal := by
  let : IsFiniteMeasure (volume.restrict W) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr hWtop⟩
  have hWreal : 0 < (volume W).toReal := ENNReal.toReal_pos hWpos.ne' hWtop
  have hfInt : Integrable (fun x => HilbertVec.ofVec (f x)) (volume.restrict W) :=
    hf.integrable one_le_two
  have hmain := eLpNorm_hilbertVec_sub_mean_le_fractionalKernel
    hW hWpos hWtop hs.le hdiam hfInt
  rw [integral_hilbertVec_poincareNormalizedVolume_eq_averageVecOn hfInt] at hmain
  have hsubMem : MemLp
      (fun x => HilbertVec.ofVec (f x - averageVecOn W f)) 2
      (volume.restrict W) := by
    have h := hf.sub (memLp_const (HilbertVec.ofVec (averageVecOn W f)))
    simpa only [← (HilbertVec.ofVecL d).map_sub, HilbertVec.ofVecL_apply] using! h
  have hleft :
      (eLpNorm
        (fun x => HilbertVec.ofVec (f x) -
          HilbertVec.ofVec (averageVecOn W f)) 2
        (poincareNormalizedVolume W)).toReal =
        vectorNormalizedL2On W (fun x => f x - averageVecOn W f) := by
    rw [show (fun x => HilbertVec.ofVec (f x) -
        HilbertVec.ofVec (averageVecOn W f)) =
      (fun x => HilbertVec.ofVec (f x - averageVecOn W f)) by
        funext x
        exact (HilbertVec.ofVecL d).map_sub _ _ |>.symm]
    exact eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq hWreal hsubMem
  have hkTop := eLpNorm_fractionalKernel_poincareNormalizedVolume_ne_top
    hWpos hWtop hs hfrac
  have hconstTop : ENNReal.ofReal (D ^ (s + (d : ℝ) / 2)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hrhsTop : ENNReal.ofReal (D ^ (s + (d : ℝ) / 2)) *
      SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2
        ((poincareNormalizedVolume W).prod
          (poincareNormalizedVolume W)) ≠ ∞ :=
    ENNReal.mul_ne_top hconstTop hkTop
  have hreal := ENNReal.toReal_mono hrhsTop hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (by
      obtain ⟨x, hx⟩ : W.Nonempty := nonempty_of_measure_ne_zero hWpos.ne'
      exact (euclideanNorm_nonneg (x - x)).trans (hdiam x hx x hx)) _),
    fractionalKernel_poincareNormalizedVolume_prod_toReal_eq hWreal hs,
    hleft] at hreal
  simpa only [mul_assoc] using! hreal

/-- The vector field splits into its mean-zero part and its constant mean in
the normalized Euclidean `L²` carrier. -/
theorem vectorNormalizedL2On_le_sub_averageVecOn_add_mean
    {W : Set (Vec d)} {f : Vec d → Vec d}
    (hWpos : 0 < (volume W).toReal)
    (hf : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W)) :
    vectorNormalizedL2On W f ≤
      vectorNormalizedL2On W (fun x => f x - averageVecOn W f) +
        euclideanNorm (averageVecOn W f) := by
  let : IsFiniteMeasure (volume.restrict W) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr
        (ENNReal.toReal_ne_zero.mp hWpos.ne').2⟩
  let A := averageVecOn W f
  have hsub : MemLp (fun x => HilbertVec.ofVec (f x - A)) 2
      (volume.restrict W) := by
    have h := hf.sub (memLp_const (HilbertVec.ofVec A))
    simpa only [← (HilbertVec.ofVecL d).map_sub, HilbertVec.ofVecL_apply] using! h
  have hconst : MemLp (fun _ : Vec d => HilbertVec.ofVec A) 2
      (volume.restrict W) := memLp_const _
  have htri : eLpNorm (fun x => HilbertVec.ofVec (f x)) 2
      (poincareNormalizedVolume W) ≤
    eLpNorm (fun x => HilbertVec.ofVec (f x - A)) 2
        (poincareNormalizedVolume W) +
      eLpNorm (fun _ : Vec d => HilbertVec.ofVec A) 2
        (poincareNormalizedVolume W) := by
    have hfun : (fun x => HilbertVec.ofVec (f x)) =
        (fun x => HilbertVec.ofVec (f x - A)) +
          (fun _ : Vec d => HilbertVec.ofVec A) := by
      funext x
      change (HilbertVec.ofVecL d) (f x) =
        (HilbertVec.ofVecL d) (f x - A) + (HilbertVec.ofVecL d) A
      rw [← (HilbertVec.ofVecL d).map_add]
      congr 1
      abel
    rw [hfun]
    exact eLpNorm_add_le one_le_two
  have hsubNorm : eLpNorm (fun x => HilbertVec.ofVec (f x - A)) 2
      (poincareNormalizedVolume W) ≠ ∞ := by
    rw [poincareNormalizedVolume]
    exact (hsub.smul_measure (ENNReal.inv_ne_top.mpr
      (ENNReal.toReal_ne_zero.mp hWpos.ne').1)).eLpNorm_ne_top
  have hconstNorm : eLpNorm (fun _ : Vec d => HilbertVec.ofVec A) 2
      (poincareNormalizedVolume W) ≠ ∞ := by
    rw [poincareNormalizedVolume]
    exact (hconst.smul_measure (ENNReal.inv_ne_top.mpr
      (ENNReal.toReal_ne_zero.mp hWpos.ne').1)).eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨hsubNorm, hconstNorm⟩) htri
  rw [ENNReal.toReal_add hsubNorm hconstNorm,
    eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq hWpos hf,
    eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq hWpos hsub,
    eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq hWpos hconst] at hreal
  have hconstant : vectorNormalizedL2On W (fun _ : Vec d => A) = euclideanNorm A := by
    unfold vectorNormalizedL2On normalizedL2On
    rw [volumeAverage_const hWpos.ne']
    exact Real.sqrt_sq (euclideanNorm_nonneg A)
  rwa [hconstant] at hreal

/-- Fractional Poincare on a truncated cube, before absorbing its explicit
diameter and volume into a dimensional constant. -/
theorem vectorNormalizedL2On_sub_averageVecOn_truncatedCube_le
    {m j : ℤ} {x : Vec d} {s : ℝ} {f : Vec d → Vec d}
    (hx : x ∈ cube d m) (hjm : j - 1 ≤ m) (hs : 0 < s)
    (hf : MemLp (fun q => HilbertVec.ofVec (f q)) 2
      (volume.restrict (truncatedCube d m j x)))
    (hfrac : fractionalSeminormOn (truncatedCube d m j x) s f ≠ ∞) :
    vectorNormalizedL2On (truncatedCube d m j x)
        (fun q => f q - averageVecOn (truncatedCube d m j x) f) ≤
      ((d : ℝ) * (3 : ℝ) ^ j) ^ (s + (d : ℝ) / 2) *
        s ^ (-(1 / 2 : ℝ)) *
        (volume (truncatedCube d m j x)).toReal ^ (-(1 / 2 : ℝ)) *
        (fractionalSeminormOn (truncatedCube d m j x) s f).toReal := by
  have hVreal := Section6ExcessDecay.volume_toReal_truncatedCube_pos x hx hjm
  have hV0 : 0 < volume (truncatedCube d m j x) := by
    exact pos_iff_ne_zero.mpr (ENNReal.toReal_ne_zero.mp hVreal.ne').1
  have hVtop : volume (truncatedCube d m j x) ≠ ∞ :=
    (Section6ExcessDecay.volume_truncatedCube_lt_top d m j x).ne
  apply vectorNormalizedL2On_sub_averageVecOn_le_fractionalSeminormOn
    (Section6ExcessDecay.measurableSet_truncatedCube d m j x)
    hV0 hVtop hs
  · intro p hp q hq
    have hdist : dist p q ≤ (3 : ℝ) ^ j := by
      have hlt := Metric.mem_ball.mp
        (Section6ExcessDecay.truncatedCube_subset_ball hp hq)
      exact le_of_lt (by simpa [dist_comm] using! hlt)
    have heu := euclideanDist_le_dimension_mul_dist p q
    unfold euclideanDist at heu
    exact heu.trans (mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg d))
  · exact hf
  · exact hfrac

/-- Restriction of the normalized Euclidean vector `L²` carrier. -/
theorem vectorNormalizedL2On_le_of_subset
    {W W' : Set (Vec d)} {f : Vec d → Vec d}
    (hsub : W' ⊆ W) (hWpos : 0 < (volume W).toReal)
    (hW'pos : 0 < (volume W').toReal)
    (hf : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W)) :
    vectorNormalizedL2On W' f ≤
      Real.sqrt ((volume W).toReal / (volume W').toReal) *
        vectorNormalizedL2On W f := by
  have hnorm : MemLp (fun x => euclideanNorm (f x)) 2 (volume.restrict W) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using! hf.norm
  unfold vectorNormalizedL2On
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_le_of_subset
    hsub hWpos hW'pos hnorm.integrable_sq

/-- Minkowski with a constant vector, in the exact Euclidean normalized
`L²` carrier. -/
theorem vectorNormalizedL2On_add_const_le
    {W : Set (Vec d)} {f : Vec d → Vec d} (A : Vec d)
    (hWpos : 0 < (volume W).toReal)
    (hf : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W)) :
    vectorNormalizedL2On W (fun x => f x + A) ≤
      vectorNormalizedL2On W f + euclideanNorm A := by
  let : IsFiniteMeasure (volume.restrict W) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr
        (ENNReal.toReal_ne_zero.mp hWpos.ne').2⟩
  have hconst : MemLp (fun _ : Vec d => HilbertVec.ofVec A) 2
      (volume.restrict W) := memLp_const _
  have hsum : MemLp (fun x => HilbertVec.ofVec (f x + A)) 2
      (volume.restrict W) := by
    have h := hf.add hconst
    simpa only [← (HilbertVec.ofVecL d).map_add, HilbertVec.ofVecL_apply] using! h
  have htri : eLpNorm (fun x => HilbertVec.ofVec (f x + A)) 2
      (poincareNormalizedVolume W) ≤
    eLpNorm (fun x => HilbertVec.ofVec (f x)) 2
        (poincareNormalizedVolume W) +
      eLpNorm (fun _ : Vec d => HilbertVec.ofVec A) 2
        (poincareNormalizedVolume W) := by
    have hfun : (fun x => HilbertVec.ofVec (f x + A)) =
        (fun x => HilbertVec.ofVec (f x)) +
          (fun _ : Vec d => HilbertVec.ofVec A) := by
      funext x
      change (HilbertVec.ofVecL d) (f x + A) =
        (HilbertVec.ofVecL d) (f x) + (HilbertVec.ofVecL d) A
      exact (HilbertVec.ofVecL d).map_add _ _
    rw [hfun]
    exact eLpNorm_add_le one_le_two
  have hfNorm : eLpNorm (fun x => HilbertVec.ofVec (f x)) 2
      (poincareNormalizedVolume W) ≠ ∞ := by
    rw [poincareNormalizedVolume]
    exact (hf.smul_measure (ENNReal.inv_ne_top.mpr
      (ENNReal.toReal_ne_zero.mp hWpos.ne').1)).eLpNorm_ne_top
  have hconstNorm : eLpNorm (fun _ : Vec d => HilbertVec.ofVec A) 2
      (poincareNormalizedVolume W) ≠ ∞ := by
    rw [poincareNormalizedVolume]
    exact (hconst.smul_measure (ENNReal.inv_ne_top.mpr
      (ENNReal.toReal_ne_zero.mp hWpos.ne').1)).eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨hfNorm, hconstNorm⟩) htri
  rw [ENNReal.toReal_add hfNorm hconstNorm,
    eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq hWpos hsum,
    eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq hWpos hf,
    eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq hWpos hconst] at hreal
  have hconstant : vectorNormalizedL2On W (fun _ : Vec d => A) = euclideanNorm A := by
    unfold vectorNormalizedL2On normalizedL2On
    rw [volumeAverage_const hWpos.ne']
    exact Real.sqrt_sq (euclideanNorm_nonneg A)
  rwa [hconstant] at hreal

/-- Local `L²` price on a subwindow, split into the ambient mean and the
ambient fractional fluctuation.  This is the form used for every projected
boundary cell. -/
theorem vectorNormalizedL2On_subwindow_le_mean_add_fractional
    {W W' : Set (Vec d)} {s D : ℝ} {f : Vec d → Vec d}
    (hsub : W' ⊆ W) (hW : MeasurableSet W)
    (hWpos : 0 < volume W) (hWtop : volume W ≠ ∞)
    (hW'pos : 0 < (volume W').toReal) (hs : 0 < s)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, euclideanNorm (x - y) ≤ D)
    (hf : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W))
    (hfrac : fractionalSeminormOn W s f ≠ ∞) :
    vectorNormalizedL2On W' f ≤
      Real.sqrt ((volume W).toReal / (volume W').toReal) *
        (D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
          (volume W).toReal ^ (-(1 / 2 : ℝ)) *
            (fractionalSeminormOn W s f).toReal) +
        euclideanNorm (averageVecOn W f) := by
  let : IsFiniteMeasure (volume.restrict W) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr hWtop⟩
  let A := averageVecOn W f
  let r : Vec d → Vec d := fun x => f x - A
  have hWreal : 0 < (volume W).toReal := ENNReal.toReal_pos hWpos.ne' hWtop
  have hr : MemLp (fun x => HilbertVec.ofVec (r x)) 2 (volume.restrict W) := by
    have h := hf.sub (memLp_const (HilbertVec.ofVec A))
    simpa only [r, ← (HilbertVec.ofVecL d).map_sub, HilbertVec.ofVecL_apply] using! h
  have hr' : MemLp (fun x => HilbertVec.ofVec (r x)) 2 (volume.restrict W') :=
    hr.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hadd := vectorNormalizedL2On_add_const_le A hW'pos hr'
  have hfun : (fun x => r x + A) = f := by
    funext x
    dsimp [r, A]
    abel
  rw [hfun] at hadd
  have hrest := vectorNormalizedL2On_le_of_subset hsub hWreal hW'pos hr
  have hpoincare := vectorNormalizedL2On_sub_averageVecOn_le_fractionalSeminormOn
    hW hWpos hWtop hs hdiam hf hfrac
  have hrEq : r = fun x => f x - averageVecOn W f := rfl
  rw [hrEq] at hrest
  calc
    vectorNormalizedL2On W' f ≤ vectorNormalizedL2On W' r + euclideanNorm A := hadd
    _ ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) *
          vectorNormalizedL2On W r + euclideanNorm A := by gcongr
    _ ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) *
          (D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
            (volume W).toReal ^ (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn W s f).toReal) +
          euclideanNorm (averageVecOn W f) := by
      dsimp [A]
      rw [hrEq]
      gcongr

/-- Jensen: the Euclidean size of the window mean is controlled by the
normalized Euclidean `L²` size. -/
theorem euclideanNorm_averageVecOn_le_vectorNormalizedL2On
    {W : Set (Vec d)} {f : Vec d → Vec d}
    (hWpos : 0 < (volume W).toReal)
    (hf : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W)) :
    euclideanNorm (averageVecOn W f) ≤ vectorNormalizedL2On W f := by
  have hpair := ENNReal.toReal_ne_zero.mp hWpos.ne'
  have := isProbabilityMeasure_poincareNormalizedVolume
    (pos_iff_ne_zero.mpr hpair.1) hpair.2
  have hfμ : MemLp (fun x => HilbertVec.ofVec (f x)) 2
      (poincareNormalizedVolume W) := by
    rw [poincareNormalizedVolume]
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr hpair.1)
  have hfInt : Integrable (fun x => HilbertVec.ofVec (f x))
      (volume.restrict W) := by
    let : IsFiniteMeasure (volume.restrict W) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.mpr hpair.2⟩
    exact hf.integrable one_le_two
  have h1 : ‖∫ x, HilbertVec.ofVec (f x) ∂(poincareNormalizedVolume W)‖ₑ ≤
      eLpNorm (fun x => HilbertVec.ofVec (f x)) 1
        (poincareNormalizedVolume W) := by
    rw [eLpNorm_one_eq_lintegral_enorm hfμ.aestronglyMeasurable]
    exact enorm_integral_le_lintegral_enorm _
  have h2 : eLpNorm (fun x => HilbertVec.ofVec (f x)) 1
      (poincareNormalizedVolume W) ≤
      eLpNorm (fun x => HilbertVec.ofVec (f x)) 2
        (poincareNormalizedVolume W) :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have htop : eLpNorm (fun x => HilbertVec.ofVec (f x)) 2
      (poincareNormalizedVolume W) ≠ ∞ := hfμ.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop (h1.trans h2)
  rw [integral_hilbertVec_poincareNormalizedVolume_eq_averageVecOn hfInt,
    ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
    ← euclideanNorm_eq_norm_ofVec,
    eLpNorm_hilbertVec_poincareNormalizedVolume_toReal_eq hWpos hf] at hreal
  exact hreal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
