module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFractionalRadial
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszFractionalComparison

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The Gagliardo kernel of an arbitrary scalar field, in the exact shape used
by `fluxRowFractionalGagliardoKernel`. -/
def fluxRowFractionalKernelOf (sigma : ℝ) (v : Vec d → ℂ)
    (z : Vec d × Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal <|
    sigma * ‖v z.1 - v z.2‖ ^ 2 /
      Real.rpow ‖z.1 - z.2‖ ((d : ℝ) + 2 * sigma)



theorem fluxRowFractionalKernelOf_inverseFourier (sigma : ℝ)
    (phi : SchwartzMap (Vec d) ℂ) :
    fluxRowFractionalKernelOf sigma (inverseFourierSchwartz phi) =
      fluxRowFractionalGagliardoKernel sigma phi := rfl

theorem measurable_fluxRowFractionalKernelOf {sigma : ℝ} {v : Vec d → ℂ}
    (hv : Measurable v) :
    Measurable (fluxRowFractionalKernelOf sigma v) := by
  have hnum : Measurable fun z : Vec d × Vec d ↦
      sigma * ‖v z.1 - v z.2‖ ^ 2 :=
    ((((hv.comp measurable_fst).sub (hv.comp measurable_snd)).norm).pow_const
      2).const_mul _
  have hden : Measurable fun z : Vec d × Vec d ↦
      Real.rpow ‖z.1 - z.2‖ ((d : ℝ) + 2 * sigma) := by
    show Measurable fun z : Vec d × Vec d ↦
      (‖z.1 - z.2‖ : ℝ) ^ ((d : ℝ) + 2 * sigma)
    fun_prop
  exact (hnum.div hden).ennreal_ofReal

/-- The commutator majorant of a `Lam`-Lipschitz, `1`-bounded cutoff. -/
def fluxRowFractionalCutoffIntegrand (d : ℕ) (sigma Lam : ℝ) (h : Vec d) :
    ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (Lam ^ 2 * ‖h‖ ^ 2) /
    Real.rpow ‖h‖ ((d : ℝ) + 2 * sigma))

/-- The total mass of the unit-Lipschitz commutator majorant. -/
def fluxRowFractionalCutoffConst (d : ℕ) (sigma : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : Vec d, fluxRowFractionalCutoffIntegrand d sigma 1 h ∂volume

theorem measurable_fluxRowFractionalCutoffIntegrand (d : ℕ) (sigma Lam : ℝ) :
    Measurable (fluxRowFractionalCutoffIntegrand d sigma Lam) := by
  have hbase : Measurable fun h : Vec d ↦
      min 1 (Lam ^ 2 * ‖h‖ ^ 2) / (‖h‖ : ℝ) ^ ((d : ℝ) + 2 * sigma) := by
    fun_prop
  exact hbase.ennreal_ofReal

/-- Pointwise dilation of the commutator majorant. -/
theorem fluxRowFractionalCutoffIntegrand_scale (d : ℕ) (sigma : ℝ) {Lam : ℝ}
    (hLam : 0 < Lam) (h : Vec d) :
    fluxRowFractionalCutoffIntegrand d sigma Lam h =
      ENNReal.ofReal (Real.rpow Lam ((d : ℝ) + 2 * sigma)) *
        fluxRowFractionalCutoffIntegrand d sigma 1 (Lam • h) := by
  have hnorm : ‖Lam • h‖ = Lam * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLam]
  have hLa : (0 : ℝ) < Real.rpow Lam ((d : ℝ) + 2 * sigma) :=
    Real.rpow_pos_of_pos hLam _
  have hrpow : Real.rpow (Lam * ‖h‖) ((d : ℝ) + 2 * sigma) =
      Real.rpow Lam ((d : ℝ) + 2 * sigma) *
        Real.rpow ‖h‖ ((d : ℝ) + 2 * sigma) :=
    Real.mul_rpow hLam.le (norm_nonneg h)
  have hnum : (1 : ℝ) ^ 2 * (Lam * ‖h‖) ^ 2 = Lam ^ 2 * ‖h‖ ^ 2 := by ring
  unfold fluxRowFractionalCutoffIntegrand
  rw [hnorm, hrpow, hnum, ← ENNReal.ofReal_mul hLa.le]
  congr 1
  rw [mul_div_assoc', mul_div_mul_left _ _ hLa.ne']

/-- Scaling of the commutator majorant's total mass. -/
theorem lintegral_fluxRowFractionalCutoffIntegrand (d : ℕ) (sigma : ℝ)
    {Lam : ℝ} (hLam : 0 < Lam) :
    ∫⁻ h : Vec d, fluxRowFractionalCutoffIntegrand d sigma Lam h ∂volume =
      ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
        fluxRowFractionalCutoffConst d sigma := by
  have hG := measurable_fluxRowFractionalCutoffIntegrand d sigma 1
  have hsmul : Measurable fun x : Vec d ↦ Lam • x := measurable_const_smul Lam
  have hfr : Module.finrank ℝ (Vec d) = d := by simp
  have hlast : Real.rpow Lam ((d : ℝ) + 2 * sigma) * |((Lam : ℝ) ^ d)⁻¹| =
      Real.rpow Lam (2 * sigma) := by
    show Lam ^ ((d : ℝ) + 2 * sigma) * |((Lam : ℝ) ^ d)⁻¹| = Lam ^ (2 * sigma)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Lam : ℝ) ^ d)⁻¹),
      Real.rpow_add hLam, Real.rpow_natCast]
    field_simp
  calc ∫⁻ h : Vec d, fluxRowFractionalCutoffIntegrand d sigma Lam h ∂volume
      = ∫⁻ h : Vec d, ENNReal.ofReal (Real.rpow Lam ((d : ℝ) + 2 * sigma)) *
          fluxRowFractionalCutoffIntegrand d sigma 1 (Lam • h) ∂volume :=
        lintegral_congr fun h ↦
          fluxRowFractionalCutoffIntegrand_scale d sigma hLam h
    _ = ENNReal.ofReal (Real.rpow Lam ((d : ℝ) + 2 * sigma)) *
          ∫⁻ h : Vec d,
            fluxRowFractionalCutoffIntegrand d sigma 1 (Lam • h) ∂volume :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.rpow Lam ((d : ℝ) + 2 * sigma)) *
          ∫⁻ k : Vec d, fluxRowFractionalCutoffIntegrand d sigma 1 k
            ∂(Measure.map (fun x : Vec d ↦ Lam • x) volume) := by
        rw [lintegral_map hG hsmul]
    _ = ENNReal.ofReal (Real.rpow Lam ((d : ℝ) + 2 * sigma)) *
          (ENNReal.ofReal |((Lam : ℝ) ^ d)⁻¹| *
            fluxRowFractionalCutoffConst d sigma) := by
        rw [Measure.map_addHaar_smul volume hLam.ne', hfr,
          lintegral_smul_measure]
        rfl
    _ = ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
          fluxRowFractionalCutoffConst d sigma := by
        have h2 := (@ENNReal.ofReal_mul (Real.rpow Lam ((d : ℝ) + 2 * sigma))
          (|((Lam : ℝ) ^ d)⁻¹|) (Real.rpow_nonneg hLam.le _)).symm
        rw [← mul_assoc, h2, hlast]

/-- The commutator majorant is dominated by the Gagliardo--Fourier majorant of
`P-230` in every positive dimension. -/
theorem fluxRowFractionalCutoffIntegrand_le_radial {d : ℕ} (hd : 0 < d)
    (sigma : ℝ) (h : Vec d) :
    fluxRowFractionalCutoffIntegrand d sigma 1 h ≤
      fluxRowFractionalRadialIntegrand d sigma 1 h := by
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnum : min 1 ((1 : ℝ) ^ 2 * ‖h‖ ^ 2) ≤
      min 4 (16 * Real.pi ^ 2 * (d : ℝ) * (1 : ℝ) ^ 2 * ‖h‖ ^ 2) := by
    apply le_min
    · exact le_trans (min_le_left _ _) (by norm_num)
    · refine le_trans (min_le_right _ _) ?_
      have : (1 : ℝ) ^ 2 ≤ 16 * Real.pi ^ 2 * (d : ℝ) * (1 : ℝ) ^ 2 := by
        nlinarith
      nlinarith [sq_nonneg ‖h‖]
  unfold fluxRowFractionalCutoffIntegrand fluxRowFractionalRadialIntegrand
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right hnum
  exact Real.rpow_nonneg (norm_nonneg h) _

/-- Finiteness of the commutator constant. -/
theorem fluxRowFractionalCutoffConst_ne_top {d : ℕ} {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    fluxRowFractionalCutoffConst d sigma ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : ∀ h : Vec 0, fluxRowFractionalCutoffIntegrand 0 sigma 1 h = 0 := by
      intro h
      have hz : h = 0 := Subsingleton.elim _ _
      have hne : 2 * sigma ≠ 0 := by positivity
      unfold fluxRowFractionalCutoffIntegrand
      rw [hz]
      norm_num [Real.zero_rpow hne]
    rw [fluxRowFractionalCutoffConst, lintegral_congr h0]
    simp
  · refine ne_top_of_le_ne_top (b := fluxRowFractionalRadialConst d sigma)
      (fluxRowFractionalRadialConst_ne_top' hsigma0 hsigma1) ?_
    exact lintegral_mono fun h ↦
      fluxRowFractionalCutoffIntegrand_le_radial hd sigma h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
