module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_lem_load_fourier_face_translation_exp_small (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ ≤ ‖x‖ := by
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

lemma aux_lem_load_fourier_face_translation_exp_large (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ ≤ 2 := by
  calc
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ ≤
        ‖Complex.exp (Complex.I * (x : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num

lemma aux_lem_load_fourier_face_translation_sine_small (x : ℝ) :
    ‖2 * Real.sin (x / 2)‖ ≤ ‖x‖ := by
  rw [← Complex.norm_exp_I_mul_ofReal_sub_one]
  exact aux_lem_load_fourier_face_translation_exp_small x

lemma aux_lem_load_fourier_face_translation_sine_large (x : ℝ) :
    ‖2 * Real.sin (x / 2)‖ ≤ 2 := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [Real.abs_sin_le_one (x / 2)]

lemma aux_lem_load_fourier_face_translation_integrable
    (s : ℝ) (hs0 : 1 / 2 < s) (hs1 : s < 3 / 2) :
    Integrable (fun x : ℝ =>
      ‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow |x| (-2 * s)) := by
  let g : ℝ → ℝ := fun x =>
    ‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow |x| (-2 * s)
  have hg_meas : Measurable g := by
    dsimp [g]
    measurability
  have hsmall_pow : IntegrableOn (fun x : ℝ => Real.rpow x (2 - 2 * s))
      (Set.Ioo 0 1) := by
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (s := 2 - 2 * s)
      (t := 1) zero_lt_one).2 (by linarith)
  have hsmall : IntegrableOn g (Set.Ioo 0 1) := by
    apply hsmall_pow.mono' (hg_meas.aestronglyMeasurable.mono_measure
      (Measure.restrict_le_self))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    have hsq : ‖2 * Real.sin (x / 2)‖ ^ 2 ≤ x ^ 2 := by
      have h := aux_lem_load_fourier_face_translation_sine_small x
      have h' : ‖2 * Real.sin (x / 2)‖ ≤ x := by
        simpa [Real.norm_eq_abs, abs_of_pos hx0] using h
      nlinarith [norm_nonneg (2 * Real.sin (x / 2))]
    have hnonneg : 0 ≤ Real.rpow x (-2 * s) :=
      Real.rpow_nonneg (le_of_lt hx0) _
    have hmul := mul_le_mul_of_nonneg_right hsq hnonneg
    have hnonneg_g : 0 ≤ ‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow |x| (-2 * s) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (abs_nonneg x) _)
    calc
      ‖g x‖ = ‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow x (-2 * s) := by
        change |‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow |x| (-2 * s)| =
          ‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow x (-2 * s)
        rw [abs_of_nonneg hnonneg_g, abs_of_pos hx0]
      _ ≤ x ^ 2 * Real.rpow x (-2 * s) := hmul
      _ = Real.rpow x (2 - 2 * s) := by
        rw [← Real.rpow_natCast]
        change Real.rpow x (2 : ℝ) * Real.rpow x (-2 * s) =
          Real.rpow x (2 - 2 * s)
        calc
          Real.rpow x (2 : ℝ) * Real.rpow x (-2 * s) =
              Real.rpow x ((2 : ℝ) + (-2 * s)) :=
            (Real.rpow_add hx0 (2 : ℝ) (-2 * s)).symm
          _ = Real.rpow x (2 - 2 * s) := by congr 1 ; ring
  have htail_pow : IntegrableOn (fun x : ℝ => Real.rpow x (-2 * s))
      (Set.Ioi 1) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have htail : IntegrableOn g (Set.Ioi 1) := by
    apply (htail_pow.const_mul 4).mono' (hg_meas.aestronglyMeasurable.mono_measure
      (Measure.restrict_le_self))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have h := aux_lem_load_fourier_face_translation_sine_large x
    have hsq : ‖2 * Real.sin (x / 2)‖ ^ 2 ≤ (4 : ℝ) := by
      nlinarith [norm_nonneg (2 * Real.sin (x / 2))]
    have hnonneg : 0 ≤ Real.rpow |x| (-2 * s) :=
      Real.rpow_nonneg (abs_nonneg x) _
    have hmul := mul_le_mul_of_nonneg_right hsq hnonneg
    have hnonneg_g : 0 ≤ ‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow |x| (-2 * s) :=
      mul_nonneg (sq_nonneg _) hnonneg
    change |‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow |x| (-2 * s)| ≤
      4 * Real.rpow x (-2 * s)
    rw [abs_of_nonneg hnonneg_g, abs_of_pos (lt_trans zero_lt_one hx1)]
    have hmul' : ‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow x (-2 * s) ≤
        4 * Real.rpow x (-2 * s) := by
      simpa [abs_of_pos (lt_trans zero_lt_one hx1)] using hmul
    exact hmul'
  have hpos : IntegrableOn g (Set.Ioi 0) := by
    have hsmall' : IntegrableOn g (Set.Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact hsmall
    have h := hsmall'.union htail
    convert h using 1
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · intro hx
      by_cases hx1 : x ≤ 1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr (by linarith)
    · rintro (⟨hx0, hx1⟩ | hx1)
      · exact hx0
      · linarith
  have hneg : IntegrableOn g (Set.Iio 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def]
    convert hpos using 1
    ext x
    dsimp [g]
    rw [show -x / 2 = -(x / 2) by ring, Real.sin_neg]
    simp [abs_neg, mul_comm]
    ring
    ext y
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
    constructor <;> intro hy <;> linarith
  have hzero : IntegrableOn g ({0} : Set ℝ) := by
    exact integrableOn_singleton (μ := volume) (f := g) (by finiteness) (by simp)
  have hunion : IntegrableOn g
      (Set.Iio 0 ∪ Set.Ioi 0 ∪ ({0} : Set ℝ)) :=
    (hneg.union hpos).union hzero
  have hall : IntegrableOn g Set.univ := by
    convert hunion using 1
    ext x
    simp only [Set.mem_union, Set.mem_univ, Set.mem_Iio, Set.mem_Ioi,
      Set.mem_singleton_iff]
    constructor
    · intro _
      by_cases hx : x = 0
      · exact Or.inr hx
      · rcases lt_or_gt_of_ne hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr hx)
    · intro _
      trivial
  simpa only [IntegrableOn, Measure.restrict_univ, g] using hall

lemma aux_lem_load_fourier_face_translation_pointwise
    (s tau xi zeta : ℝ) (hs : 0 < s) (htau : 0 < tau) (hxi : xi ≠ 0) :
    ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
        Real.rpow (1 + xi ^ 2 + zeta ^ 2) (-s) ≤
      Real.rpow tau (2 * s) *
        (‖2 * Real.sin ((tau * xi) / 2)‖ ^ 2 *
          Real.rpow |tau * xi| (-2 * s)) := by
  have hbase : xi ^ 2 ≤ 1 + xi ^ 2 + zeta ^ 2 := by
    nlinarith [sq_nonneg xi, sq_nonneg zeta]
  have hxi2 : 0 < xi ^ 2 := sq_pos_of_ne_zero hxi
  have hrpow : Real.rpow (1 + xi ^ 2 + zeta ^ 2) (-s) ≤
      Real.rpow (xi ^ 2) (-s) := by
    exact Real.rpow_le_rpow_of_nonpos hxi2 hbase (neg_nonpos.mpr hs.le)
  have hxi_rpow : Real.rpow (xi ^ 2) (-s) = Real.rpow |xi| (-2 * s) := by
    rw [← sq_abs]
    rw [← Real.rpow_natCast]
    calc
      Real.rpow (Real.rpow |xi| (2 : ℝ)) (-s) =
          Real.rpow |xi| ((2 : ℝ) * (-s)) := by
            exact (Real.rpow_mul (abs_nonneg xi) (2 : ℝ) (-s)).symm
      _ = Real.rpow |xi| (-2 * s) := by congr 1 ; ring
  have hscale : Real.rpow tau (2 * s) * Real.rpow |tau * xi| (-2 * s) =
      Real.rpow |xi| (-2 * s) := by
    have habs : |tau * xi| = tau * |xi| := by
      rw [abs_mul, abs_of_pos htau]
    rw [habs]
    have hmulrpow : Real.rpow (tau * |xi|) (-2 * s) =
        Real.rpow tau (-2 * s) * Real.rpow |xi| (-2 * s) :=
      Real.mul_rpow (le_of_lt htau) (abs_nonneg xi)
    rw [hmulrpow]
    calc
      Real.rpow tau (2 * s) *
          (Real.rpow tau (-2 * s) * Real.rpow |xi| (-2 * s)) =
          (Real.rpow tau (2 * s) * Real.rpow tau (-2 * s)) *
            Real.rpow |xi| (-2 * s) := by ring
      _ = Real.rpow |xi| (-2 * s) := by
        calc
          (Real.rpow tau (2 * s) * Real.rpow tau (-2 * s)) *
              Real.rpow |xi| (-2 * s) =
              Real.rpow tau ((2 * s) + (-2 * s)) *
                Real.rpow |xi| (-2 * s) := by
                  exact congrArg (fun q : ℝ => q * Real.rpow |xi| (-2 * s))
                    (Real.rpow_add htau (2 * s) (-2 * s)).symm
          _ = Real.rpow |xi| (-2 * s) := by norm_num
  calc
    ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
        Real.rpow (1 + xi ^ 2 + zeta ^ 2) (-s) ≤
      ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
        Real.rpow (xi ^ 2) (-s) := by
          gcongr
    _ = ‖2 * Real.sin ((tau * xi) / 2)‖ ^ 2 *
        Real.rpow (xi ^ 2) (-s) := by
          have hexp : ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ =
              ‖2 * Real.sin ((tau * xi) / 2)‖ := by
            convert Complex.norm_exp_I_mul_ofReal_sub_one (tau * xi) using 1 ;
              push_cast ; ring
          rw [hexp]
    _ = Real.rpow tau (2 * s) *
        (‖2 * Real.sin ((tau * xi) / 2)‖ ^ 2 *
          Real.rpow |tau * xi| (-2 * s)) := by
          rw [hxi_rpow]
          rw [← hscale]
          ring



theorem lem_load_fourier_face_translation :
  ∀ (s : ℝ), 1 / 2 < s → s < 3 / 2 →
    ∃ C_s : ℝ, 0 < C_s ∧
      ∀ (d : ℕ) (_hd : 2 ≤ d) (tau : ℝ), 0 < tau →
        ∀ (zeta : SpatialCoordinates (d - 1)),
          ∫ xi : ℝ,
              ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
              Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s) ≤
            C_s * tau ^ (2 * s - 1) := by
  intro s hs0 hs1
  let g : ℝ → ℝ := fun x =>
    ‖2 * Real.sin (x / 2)‖ ^ 2 * Real.rpow |x| (-2 * s)
  have hg : Integrable g := by
    simpa [g] using
      (aux_lem_load_fourier_face_translation_integrable s hs0 hs1)
  have hI_nonneg : 0 ≤ ∫ x : ℝ, g x := by
    apply integral_nonneg
    intro x
    dsimp [g]
    positivity
  refine ⟨(∫ x : ℝ, g x) + 1, by linarith, ?_⟩
  intro d hd tau htau zeta
  have hspos : 0 < s := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hs0
  have hscale_integrable : Integrable (fun x : ℝ => g (tau * x)) :=
    hg.comp_mul_left' htau.ne'
  have hmajor_integrable : Integrable (fun x : ℝ =>
      Real.rpow tau (2 * s) * g (tau * x)) :=
    hscale_integrable.const_mul _
  have hF_meas : AEStronglyMeasurable (fun xi : ℝ =>
      ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
        Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s)) := by
    have hmeas : Measurable (fun xi : ℝ =>
        ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
          Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s)) := by
      measurability
    exact hmeas.aestronglyMeasurable
  have hF_nonneg (xi : ℝ) : 0 ≤
      ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
        Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s) := by
    have hbase : 0 ≤ 1 + xi ^ 2 + ‖zeta‖ ^ 2 := by positivity
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hbase _)
  have hxi_ae : ∀ᵐ xi : ℝ, xi ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hbound (xi : ℝ) (hxi : xi ≠ 0) :
      ‖‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
          Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s)‖ ≤
        Real.rpow tau (2 * s) * g (tau * xi) := by
    have hp := aux_lem_load_fourier_face_translation_pointwise
      s tau xi ‖zeta‖ hspos htau hxi
    have hbase : 0 ≤ 1 + xi ^ 2 + ‖zeta‖ ^ 2 := by positivity
    have hpow : 0 ≤ Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s) :=
      Real.rpow_nonneg hbase _
    have hprod : 0 ≤ ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
        Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s) :=
      mul_nonneg (sq_nonneg _) hpow
    change |‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
        Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s)| ≤
      Real.rpow tau (2 * s) * g (tau * xi)
    rw [abs_of_nonneg hprod]
    simpa [g, Real.norm_eq_abs] using hp
  have hF_integrable : Integrable (fun xi : ℝ =>
      ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
        Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s)) := by
    apply hmajor_integrable.mono' hF_meas
    filter_upwards [hxi_ae] with xi hxi
    exact hbound xi hxi
  have h_integral_mono :
      (∫ xi : ℝ,
        ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
          Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s)) ≤
        ∫ xi : ℝ, Real.rpow tau (2 * s) * g (tau * xi) :=
    integral_mono_ae hF_integrable hmajor_integrable
      (hxi_ae.mono fun xi hxi => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg xi)] using
          hbound xi hxi)
  have h_integral_scale :
      (∫ xi : ℝ, Real.rpow tau (2 * s) * g (tau * xi)) =
        Real.rpow tau (2 * s - 1) * (∫ x : ℝ, g x) := by
    calc
      (∫ xi : ℝ, Real.rpow tau (2 * s) * g (tau * xi)) =
          Real.rpow tau (2 * s) * (∫ xi : ℝ, g (tau * xi)) := by
            rw [integral_const_mul]
      _ = Real.rpow tau (2 * s) *
          (|tau⁻¹| * (∫ x : ℝ, g x)) := by
            rw [Measure.integral_comp_mul_left]
            rfl
      _ = Real.rpow tau (2 * s - 1) * (∫ x : ℝ, g x) := by
            rw [abs_of_pos (inv_pos.mpr htau)]
            calc
              Real.rpow tau (2 * s) * (tau⁻¹ * (∫ x : ℝ, g x)) =
                  (Real.rpow tau (2 * s) * tau⁻¹) * (∫ x : ℝ, g x) := by ring
              _ = Real.rpow tau (2 * s - 1) * (∫ x : ℝ, g x) := by
                congr 1
                rw [← Real.rpow_neg_one]
                calc
                  Real.rpow tau (2 * s) * Real.rpow tau (-1) =
                      Real.rpow tau ((2 * s) + (-1)) := by
                        exact (Real.rpow_add htau (2 * s) (-1)).symm
                  _ = Real.rpow tau (2 * s - 1) := by congr 1
  have htau_power : 0 < Real.rpow tau (2 * s - 1) :=
    Real.rpow_pos_of_pos htau _
  calc
    (∫ xi : ℝ,
        ‖Complex.exp (Complex.I * (tau * xi : ℂ)) - 1‖ ^ 2 *
          Real.rpow (1 + xi ^ 2 + ‖zeta‖ ^ 2) (-s)) ≤
        ∫ xi : ℝ, Real.rpow tau (2 * s) * g (tau * xi) := h_integral_mono
    _ = Real.rpow tau (2 * s - 1) * (∫ x : ℝ, g x) := h_integral_scale
    _ ≤ ((∫ x : ℝ, g x) + 1) * Real.rpow tau (2 * s - 1) := by
      calc
        Real.rpow tau (2 * s - 1) * (∫ x : ℝ, g x) ≤
            Real.rpow tau (2 * s - 1) * (∫ x : ℝ, g x) +
              Real.rpow tau (2 * s - 1) := by linarith
        _ = ((∫ x : ℝ, g x) + 1) * Real.rpow tau (2 * s - 1) := by ring

end SubdiffusiveProcess.Paper
