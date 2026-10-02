import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFractionalPlancherel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section

/-- The radial majorant of the fractional difference kernel at frequency
size `T`. -/
def fluxRowFractionalRadialIntegrand (d : ℕ) (sigma T : ℝ) (h : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (min 4 (16 * Real.pi ^ 2 * d * T ^ 2 * ‖h‖ ^ 2) /
    Real.rpow ‖h‖ ((d : ℝ) + 2 * sigma))

/-- The total mass of the unit-frequency radial majorant. -/
def fluxRowFractionalRadialConst (d : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : Vec d, fluxRowFractionalRadialIntegrand d sigma 1 h ∂volume

theorem measurable_fluxRowFractionalRadialIntegrand (d : ℕ) (sigma T : ℝ) :
    Measurable (fluxRowFractionalRadialIntegrand d sigma T) := by
  have hbase : Measurable fun h : Vec d ↦
      min 4 (16 * Real.pi ^ 2 * d * T ^ 2 * ‖h‖ ^ 2) /
        (‖h‖ : ℝ) ^ ((d : ℝ) + 2 * sigma) := by fun_prop
  exact hbase.ennreal_ofReal

/-- Pointwise scaling of the radial majorant. -/
theorem fluxRowFractionalRadialIntegrand_scale (d : ℕ) (sigma : ℝ) {T : ℝ}
    (hT : 0 < T) (h : Vec d) :
    fluxRowFractionalRadialIntegrand d sigma T h =
      ENNReal.ofReal (Real.rpow T ((d : ℝ) + 2 * sigma)) *
        fluxRowFractionalRadialIntegrand d sigma 1 (T • h) := by
  have hnorm : ‖T • h‖ = T * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]
  have hTa : (0 : ℝ) < Real.rpow T ((d : ℝ) + 2 * sigma) :=
    Real.rpow_pos_of_pos hT _
  have hrpow : Real.rpow (T * ‖h‖) ((d : ℝ) + 2 * sigma) =
      Real.rpow T ((d : ℝ) + 2 * sigma) * Real.rpow ‖h‖ ((d : ℝ) + 2 * sigma) :=
    Real.mul_rpow hT.le (norm_nonneg h)
  have hnum : 16 * Real.pi ^ 2 * (d : ℝ) * (1 : ℝ) ^ 2 * (T * ‖h‖) ^ 2 =
      16 * Real.pi ^ 2 * (d : ℝ) * T ^ 2 * ‖h‖ ^ 2 := by ring
  unfold fluxRowFractionalRadialIntegrand
  rw [hnorm, hrpow, hnum, ← ENNReal.ofReal_mul hTa.le]
  congr 1
  rw [mul_div_assoc', mul_div_mul_left _ _ hTa.ne']

/-- Finiteness of the radial constant. -/
theorem fluxRowFractionalRadialConst_ne_top {d : ℕ} (hd : 0 < d) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    fluxRowFractionalRadialConst d sigma ≠ ⊤ := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  haveI : Inhabited (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nontrivial (Vec d) := Pi.nontrivial
  set F : ℝ → ℝ := fun t ↦
    min 4 (16 * Real.pi ^ 2 * (d : ℝ) * (1 : ℝ) ^ 2 * t ^ 2) /
      t ^ ((d : ℝ) + 2 * sigma) with hF
  have hmeasF : Measurable fun y : ℝ ↦ y ^ (d - 1) • F y := by
    rw [hF]; fun_prop
  have hy_pow : ∀ y : ℝ, 0 < y → (y ^ (d - 1) : ℝ) = y ^ ((d : ℝ) - 1) := by
    intro y _
    rw [show ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) by
          have h1 : (1 : ℕ) ≤ d := hd
          rw [Nat.cast_sub h1]
          norm_num,
      Real.rpow_natCast]
  have hval : ∀ y : ℝ, 0 < y → y ^ (d - 1) • F y =
      min 4 (16 * Real.pi ^ 2 * (d : ℝ) * (1 : ℝ) ^ 2 * y ^ 2) *
        y ^ (-1 - 2 * sigma) := by
    intro y hy
    rw [smul_eq_mul, hy_pow y hy, hF]
    simp only
    rw [show (-1 - 2 * sigma : ℝ) = ((d : ℝ) - 1) - ((d : ℝ) + 2 * sigma) by ring,
      Real.rpow_sub hy ((d : ℝ) - 1) ((d : ℝ) + 2 * sigma)]
    generalize (y ^ ((d : ℝ) - 1) : ℝ) = A
    generalize (y ^ ((d : ℝ) + 2 * sigma) : ℝ) = B
    ring
  have hminnonneg : ∀ y : ℝ,
      0 ≤ min 4 (16 * Real.pi ^ 2 * (d : ℝ) * (1 : ℝ) ^ 2 * y ^ 2) := by
    intro y
    exact le_min (by norm_num) (by positivity)
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioo 0 1 ∪ Set.Ici 1 := by
    ext y
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
    constructor
    · intro hy
      rcases lt_or_ge y 1 with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · linarith
  have hprof : IntegrableOn
      (fun y : ℝ ↦ y ^ (Module.finrank ℝ (Vec d) - 1) • F y) (Set.Ioi 0) volume := by
    have hfr : Module.finrank ℝ (Vec d) = d := by simp
    rw [hfr, hsplit]
    refine IntegrableOn.union ?_ ?_
    · have hmaj : IntegrableOn
          (fun y : ℝ ↦ 16 * Real.pi ^ 2 * (d : ℝ) * y ^ (1 - 2 * sigma))
          (Set.Ioo 0 1) volume :=
        ((intervalIntegral.integrableOn_Ioo_rpow_iff
          (s := 1 - 2 * sigma) (t := 1) one_pos).2 (by linarith)).const_mul _
      refine Integrable.mono' hmaj hmeasF.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      have hy0 : (0 : ℝ) < y := hy.1
      have hpos : (0 : ℝ) < y ^ (-1 - 2 * sigma) := Real.rpow_pos_of_pos hy0 _
      have hle : min 4 (16 * Real.pi ^ 2 * (d : ℝ) * (1 : ℝ) ^ 2 * y ^ 2) ≤
          16 * Real.pi ^ 2 * (d : ℝ) * y ^ 2 := by
        refine (min_le_right _ _).trans_eq ?_
        ring
      have hpow2 : (y : ℝ) ^ (2 : ℕ) * y ^ (-1 - 2 * sigma) = y ^ (1 - 2 * sigma) := by
        rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy0]
        congr 1
        push_cast
        ring
      rw [hval y hy0, Real.norm_of_nonneg (by positivity)]
      calc min 4 (16 * Real.pi ^ 2 * (d : ℝ) * (1 : ℝ) ^ 2 * y ^ 2) *
            y ^ (-1 - 2 * sigma)
          ≤ (16 * Real.pi ^ 2 * (d : ℝ) * y ^ 2) * y ^ (-1 - 2 * sigma) :=
            mul_le_mul_of_nonneg_right hle hpos.le
        _ = 16 * Real.pi ^ 2 * (d : ℝ) * y ^ (1 - 2 * sigma) := by
            rw [mul_assoc, hpow2]
    · have hIoi : IntegrableOn (fun y : ℝ ↦ (4 : ℝ) * y ^ (-1 - 2 * sigma))
          (Set.Ioi 1) volume :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
      have hmaj : IntegrableOn (fun y : ℝ ↦ (4 : ℝ) * y ^ (-1 - 2 * sigma))
          (Set.Ici 1) volume := hIoi.congr_set_ae Ioi_ae_eq_Ici.symm
      refine Integrable.mono' hmaj hmeasF.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
      have hy0 : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
      have hpos : (0 : ℝ) < y ^ (-1 - 2 * sigma) := Real.rpow_pos_of_pos hy0 _
      rw [hval y hy0, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) hpos.le
  have hint : Integrable (fun h : Vec d ↦ F ‖h‖) volume :=
    (integrable_fun_norm_addHaar volume).2 hprof
  refine ne_top_of_le_ne_top hint.hasFiniteIntegral.ne ?_
  refine lintegral_mono fun h ↦ ?_
  calc fluxRowFractionalRadialIntegrand d sigma 1 h
      = ENNReal.ofReal (F ‖h‖) := rfl
    _ ≤ ENNReal.ofReal |F ‖h‖| := ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ‖F ‖h‖‖ₑ := by rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]

/-- Scaling of the radial majorant integral. -/
theorem lintegral_fluxRowFractionalRadialIntegrand (d : ℕ) (sigma : ℝ) {T : ℝ}
    (hT : 0 < T) :
    ∫⁻ h : Vec d, fluxRowFractionalRadialIntegrand d sigma T h ∂volume =
      ENNReal.ofReal (Real.rpow T (2 * sigma)) *
        fluxRowFractionalRadialConst d sigma := by
  have hG := measurable_fluxRowFractionalRadialIntegrand d sigma 1
  have hsmul : Measurable fun x : Vec d ↦ T • x := measurable_const_smul T
  have hfr : Module.finrank ℝ (Vec d) = d := by simp
  have hlast : Real.rpow T ((d : ℝ) + 2 * sigma) * |((T : ℝ) ^ d)⁻¹| =
      Real.rpow T (2 * sigma) := by
    show T ^ ((d : ℝ) + 2 * sigma) * |((T : ℝ) ^ d)⁻¹| = T ^ (2 * sigma)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((T : ℝ) ^ d)⁻¹),
      Real.rpow_add hT, Real.rpow_natCast]
    field_simp
  calc ∫⁻ h : Vec d, fluxRowFractionalRadialIntegrand d sigma T h ∂volume
      = ∫⁻ h : Vec d, ENNReal.ofReal (Real.rpow T ((d : ℝ) + 2 * sigma)) *
          fluxRowFractionalRadialIntegrand d sigma 1 (T • h) ∂volume :=
        lintegral_congr fun h ↦
          fluxRowFractionalRadialIntegrand_scale d sigma hT h
    _ = ENNReal.ofReal (Real.rpow T ((d : ℝ) + 2 * sigma)) *
          ∫⁻ h : Vec d,
            fluxRowFractionalRadialIntegrand d sigma 1 (T • h) ∂volume :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.rpow T ((d : ℝ) + 2 * sigma)) *
          ∫⁻ k : Vec d, fluxRowFractionalRadialIntegrand d sigma 1 k
            ∂(Measure.map (fun x : Vec d ↦ T • x) volume) := by
        rw [lintegral_map hG hsmul]
    _ = ENNReal.ofReal (Real.rpow T ((d : ℝ) + 2 * sigma)) *
          (ENNReal.ofReal |((T : ℝ) ^ d)⁻¹| *
            fluxRowFractionalRadialConst d sigma) := by
        rw [Measure.map_addHaar_smul volume hT.ne', hfr, lintegral_smul_measure]
        rfl
    _ = ENNReal.ofReal (Real.rpow T (2 * sigma)) *
          fluxRowFractionalRadialConst d sigma := by
        have h2 := (@ENNReal.ofReal_mul (Real.rpow T ((d : ℝ) + 2 * sigma))
          (|((T : ℝ) ^ d)⁻¹|) (Real.rpow_nonneg hT.le _)).symm
        rw [← mul_assoc, h2, hlast]

/-- In dimension zero the radial majorant vanishes identically. -/
theorem fluxRowFractionalRadialConst_zero (sigma : ℝ) :
    fluxRowFractionalRadialConst 0 sigma = 0 := by
  have h0 : ∀ h : Vec 0, fluxRowFractionalRadialIntegrand 0 sigma 1 h = 0 := by
    intro h
    unfold fluxRowFractionalRadialIntegrand
    norm_num
  rw [fluxRowFractionalRadialConst, lintegral_congr h0]
  simp

/-- Finiteness of the radial constant in every dimension. -/
theorem fluxRowFractionalRadialConst_ne_top' {d : ℕ} {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    fluxRowFractionalRadialConst d sigma ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [fluxRowFractionalRadialConst_zero]
    simp
  · exact fluxRowFractionalRadialConst_ne_top hd hsigma0 hsigma1


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
