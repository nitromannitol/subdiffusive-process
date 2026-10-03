module

public import SubdiffusiveProcess.Paper.aux_macro_moment_bank
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Analysis.InfraredExpMomentBound
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

/-!
# The global-energy bank at a finite infrared truncation

For `H = H_L`, `L ≥ 0`, the Dirichlet energy on a working cube `Q(z,r)`, `r ≤ 1`, is at most
`K_N (K_f + C_φ)²` with a random `K_N` of finite moment; the auxiliary cross bank bounds the
energy of the characterized coefficient on the same solution.  The truncated coefficient is the
characterized one times `e^{H_L - H}`, so coercivity and response transfer with the weight
`e^{‖H_L‖ + ‖H‖}` on `Q̄(z,r)`.  Not claimed: constants uniform in the model (Stage 2).
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The cutoff coefficient changes by the pointwise factor `exp (H₂ - H₁)` when the infrared
field `H₁` is replaced by `H₂`. -/
theorem aux_prop_growth_trunc_bank_ratio {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H₁ H₂ : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (y : SpatialCoordinates d) :
    cutoffCoefficient M H₂ om N y =
      cutoffCoefficient M H₁ om N y * Real.exp (H₂ om y - H₁ om y) := by
  unfold cutoffCoefficient cutoffPotential
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Energy transfer** from the characterized coefficient to another infrared field. -/
theorem aux_prop_growth_trunc_bank_energy_transfer {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H HT : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (D : ℝ) (hD : ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      |HT om y - H om y| ≤ D)
    (Kc : ℝ)
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kc * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hF : AEMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂(volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hsol : SolvesDirichlet (cutoffPositiveCoefficient M HT om N z hr) F b u) (Kb : ℝ)
    (hbd : dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
      Kb * Cphi ^ 2) :
    sobolevCoefficientForm (cutoffPositiveCoefficient M HT om N z hr)
        (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) ≤
      (|Real.exp D * Kb| +
        ((measureUnivNNReal (volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^
            ((2 : ℝ≥0∞).toReal⁻¹)) ^ 2 *
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
            |(|Kc| * Real.exp D)|) *
        (Kf + Cphi) ^ 2 := by
  set aH := cutoffPositiveCoefficient M H om N z hr with haH
  set aT := cutoffPositiveCoefficient M HT om N z hr with haT
  have hmem := ae_restrict_mem (μ := volume) (centeredCube z r hr).isOpen.measurableSet
  have hHae := aux_prop_growth_macro_energy_coeff_ae M H om N z hr
  have hTae := aux_prop_growth_macro_energy_coeff_ae M HT om N z hr
  have hpos : ∀ y, 0 < cutoffCoefficient M H om N y := fun y =>
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  have hl : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      Real.exp (-D) * aH.val x ≤ aT.val x := by
    filter_upwards [hHae, hTae, hmem] with y h1 h2 hy
    rw [h1, h2, aux_prop_growth_trunc_bank_ratio M H HT om N y, mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hpos y).le
    have := hD y (centeredCube_subset_closedCube z hr hy)
    have := neg_abs_le (HT om y - H om y)
    linarith
  have hu : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      aT.val x ≤ Real.exp D * aH.val x := by
    filter_upwards [hHae, hTae, hmem] with y h1 h2 hy
    rw [h1, h2, aux_prop_growth_trunc_bank_ratio M H HT om N y, mul_comm (Real.exp D)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hpos y).le
    have := hD y (centeredCube_subset_closedCube z hr hy)
    have := le_abs_self (HT om y - H om y)
    linarith
  have hresp : dirichletResponse (killedResponseSpace hP) aT b ≤ (Real.exp D * Kb) * Cphi ^ 2 := by
    have h := (dirichletResponse_exp_comparison (killedResponseSpace hP) aH aT b D hl hu).2
    calc _ ≤ Real.exp D * dirichletResponse (killedResponseSpace hP) aH b := h
      _ ≤ Real.exp D * (Kb * Cphi ^ 2) :=
          mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le
      _ = (Real.exp D * Kb) * Cphi ^ 2 := by ring
  have hHle : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      aH.val x ≤ (scalePositiveCoefficient (Real.exp D) (Real.exp_pos D) aT).val x := by
    filter_upwards [hl, scalePositiveCoefficient_coeFn (Real.exp D) (Real.exp_pos D) aT]
      with x hx hs
    rw [hs]
    have h2 : aH.val x = Real.exp D * (Real.exp (-D) * aH.val x) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rw [h2]
    exact mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
  have hcoerT : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        (|Kc| * Real.exp D) * sobolevCoefficientForm aT
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) := by
    intro v
    have h1 := hcoer v
    have hf0 := sobolevCoefficientForm_nonneg aH (v : SobolevData (centeredCube z r hr))
    have h2 : sobolevCoefficientForm aH (v : SobolevData (centeredCube z r hr))
        (v : SobolevData (centeredCube z r hr)) ≤
        Real.exp D * sobolevCoefficientForm aT (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)) := by
      have := sobolevCoefficientForm_mono aH
        (scalePositiveCoefficient (Real.exp D) (Real.exp_pos D) aT) hHle
        (v : SobolevData (centeredCube z r hr))
      rwa [sobolevCoefficientForm_scale] at this
    calc _ ≤ Kc * sobolevCoefficientForm aH (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)) := h1
      _ ≤ |Kc| * sobolevCoefficientForm aH (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)) :=
          mul_le_mul_of_nonneg_right (le_abs_self Kc) hf0
      _ ≤ |Kc| * (Real.exp D * sobolevCoefficientForm aT
            (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg Kc)
      _ = _ := by ring
  exact aux_aux_macro_moment_bank_energy_le_bd hd z r hr hr1 hP aT (|Kc| * Real.exp D) hcoerT
    F Kf hKf hF hFb phi Cphi hphi hC b u hsol (Real.exp D * Kb) hresp

/-- The reference factor of a finite infrared truncation: `exp ‖H_L|_K‖` is measurable, dominates
`exp |H_L|` on `K`, and has every finite moment. -/
theorem aux_prop_growth_trunc_bank_reference {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (K : Compacts (SpatialCoordinates d)) (Q : ℝ) (hQ : 1 ≤ Q) :
    Measurable (fun om =>
        Real.exp ‖(infraredPartialSum om L).restrict (K : Set (SpatialCoordinates d))‖) ∧
      (∀ om, ∀ x ∈ (K : Set (SpatialCoordinates d)),
        Real.exp (|infraredPartialSum om L x|) ≤
          Real.exp ‖(infraredPartialSum om L).restrict (K : Set (SpatialCoordinates d))‖) ∧
      MemLp (fun om =>
          Real.exp ‖(infraredPartialSum om L).restrict (K : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure := by
  have hmeas : Measurable (fun om =>
      Real.exp ‖(infraredPartialSum om L).restrict (K : Set (SpatialCoordinates d))‖) := by
    have hc : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        Real.exp ‖f.restrict (K : Set (SpatialCoordinates d))‖) :=
      Real.continuous_exp.comp (continuous_norm.comp
        (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))))
    exact hc.measurable.comp (continuous_infraredPartialSum L).measurable
  refine ⟨hmeas, ?_, ?_⟩
  · intro om x hx
    refine Real.exp_le_exp.2 ?_
    have h := ContinuousMap.norm_coe_le_norm
      ((infraredPartialSum om L).restrict (K : Set (SpatialCoordinates d))) ⟨x, hx⟩
    have heq : ‖((infraredPartialSum om L).restrict (K : Set (SpatialCoordinates d))) ⟨x, hx⟩‖ =
        |infraredPartialSum om L x| := Real.norm_eq_abs _
    rw [heq] at h
    exact h
  · obtain ⟨C, _, hexp⟩ := infraredCharacterization_truncation_exp_moment_bound (d := d) hd
    have hint := (hexp M K Q (by linarith) L).1
    have hQ0 : ENNReal.ofReal Q ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    refine (integrable_norm_rpow_iff hmeas.aestronglyMeasurable hQ0
      ENNReal.ofReal_ne_top).1 ?_
    refine hint.congr (Filter.Eventually.of_forall fun om => ?_)
    have hbr : ‖restrictC K (infraredPartialSum om L)‖ =
        ‖(infraredPartialSum om L).restrict (K : Set (SpatialCoordinates d))‖ := rfl
    simp only [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ Q)]
    rw [hbr, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]

/-- The exponentiated sup of a continuous field on the closed working cube `Q̄(z,r)`. -/
def aux_prop_growth_trunc_bank_refFactor {d : ℕ} (f : C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) : ℝ :=
  Real.exp ‖f.restrict (closedCube z r hr : Set (SpatialCoordinates d))‖

/-- The deterministic constant of the energy majorant on the working cube. -/
def aux_prop_growth_trunc_bank_c2 {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) : ℝ :=
  ((measureUnivNNReal (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹)) ^ 2 *
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d))

theorem aux_prop_growth_trunc_bank_c2_nonneg {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    0 ≤ aux_prop_growth_trunc_bank_c2 z r hr :=
  mul_nonneg (sq_nonneg _) measureReal_nonneg

/-- The field difference on the closed cube is bounded by the sum of the two sup norms. -/
theorem aux_prop_growth_trunc_bank_diff_le {d : ℕ} (f g : C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      |f y - g y| ≤ ‖f.restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ +
        ‖g.restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ := by
  intro y hy
  have h1 := ContinuousMap.norm_coe_le_norm
    (f.restrict (closedCube z r hr : Set (SpatialCoordinates d))) ⟨y, hy⟩
  have h2 := ContinuousMap.norm_coe_le_norm
    (g.restrict (closedCube z r hr : Set (SpatialCoordinates d))) ⟨y, hy⟩
  have e1 : ‖(f.restrict (closedCube z r hr : Set (SpatialCoordinates d))) ⟨y, hy⟩‖ = |f y| :=
    Real.norm_eq_abs _
  have e2 : ‖(g.restrict (closedCube z r hr : Set (SpatialCoordinates d))) ⟨y, hy⟩‖ = |g y| :=
    Real.norm_eq_abs _
  rw [e1] at h1
  rw [e2] at h2
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- Pathwise energy bound for a target field `HT` from the reference field's coercivity constant
`K_c` and response constant `K_b`: the transfer weight is `exp ‖HT‖ · exp ‖H‖` on `Q̄(z,r)`. -/
theorem aux_prop_growth_trunc_bank_energy_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H HT : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (Kc : ℝ)
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kc * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hF : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hsol : SolvesDirichlet (cutoffPositiveCoefficient M HT om N z hr) F b u) (Kb : ℝ)
    (hbd : dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
      Kb * Cphi ^ 2) :
    sobolevCoefficientForm (cutoffPositiveCoefficient M HT om N z hr)
        (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) ≤
      aux_prop_growth_trunc_bank_refFactor (HT om) z r hr * aux_prop_growth_trunc_bank_refFactor (H om) z r hr *
        (|Kb| + aux_prop_growth_trunc_bank_c2 z r hr * |Kc|) * (Kf + Cphi) ^ 2 := by
  have h := aux_prop_growth_trunc_bank_energy_transfer hd M H HT om N z r hr hr1 hP
    (‖(HT om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ +
      ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖)
    (aux_prop_growth_trunc_bank_diff_le (HT om) (H om) z r hr) Kc hcoer F Kf hKf hF hFb phi Cphi hphi hC b u
    hsol Kb hbd
  refine h.trans (le_of_eq ?_)
  unfold aux_prop_growth_trunc_bank_refFactor aux_prop_growth_trunc_bank_c2
  rw [abs_mul (Real.exp _), abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (mul_nonneg (abs_nonneg Kc) (Real.exp_pos _).le), Real.exp_add]
  ring

/-- Moments of the transfer constant `R_T R_H (|A| + c |B|)` by Hölder's inequality. -/
theorem aux_prop_growth_trunc_bank_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : ℝ) (hQ : 1 ≤ Q) (RT RH : Ω → ℝ)
    (hRT : MemLp RT (ENNReal.ofReal (2 * (2 * Q))) μ)
    (hRH : MemLp RH (ENNReal.ofReal (2 * (2 * Q))) μ)
    (A B : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) (CA CB : ℝ)
    (hA : MemLp A (ENNReal.ofReal (2 * Q)) μ)
    (hAb : eLpNorm A (ENNReal.ofReal (2 * Q)) μ ≤ ENNReal.ofReal CA)
    (hB : MemLp B (ENNReal.ofReal (2 * Q)) μ)
    (hBb : eLpNorm B (ENNReal.ofReal (2 * Q)) μ ≤ ENNReal.ofReal CB) :
    MemLp (fun om => RT om * RH om * (|A om| + c * |B om|)) (ENNReal.ofReal Q) μ ∧
      eLpNorm (fun om => RT om * RH om * (|A om| + c * |B om|)) (ENNReal.ofReal Q) μ ≤
        eLpNorm RT (ENNReal.ofReal (2 * (2 * Q))) μ * eLpNorm RH (ENNReal.ofReal (2 * (2 * Q))) μ *
          (ENNReal.ofReal CA + ENNReal.ofReal c * ENNReal.ofReal CB) := by
  have hAs : AEStronglyMeasurable (fun om => |A om|) μ :=
    continuous_abs.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hBs : AEStronglyMeasurable (fun om => c * |B om|) μ :=
    (continuous_abs.comp_aestronglyMeasurable hB.aestronglyMeasurable).const_mul c
  have hYs : AEStronglyMeasurable (fun om => |A om| + c * |B om|) μ := hAs.add hBs
  have hEs : AEStronglyMeasurable (fun om => RT om * RH om) μ := hRT.aestronglyMeasurable.mul hRH.aestronglyMeasurable
  have hE : eLpNorm (fun om => RT om * RH om) (ENNReal.ofReal (2 * Q)) μ ≤
      eLpNorm RT (ENNReal.ofReal (2 * (2 * Q))) μ *
        eLpNorm RH (ENNReal.ofReal (2 * (2 * Q))) μ :=
    aux_aux_macro_moment_bank_product_moment μ (2 * Q) RT RH hRT.aestronglyMeasurable hRH.aestronglyMeasurable
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * Q) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hAn : eLpNorm (fun om => |A om|) (ENNReal.ofReal (2 * Q)) μ ≤ ENNReal.ofReal CA := by
    have h := eLpNorm_norm (p := ENNReal.ofReal (2 * Q)) (μ := μ) (f := A) hA.aestronglyMeasurable
    simp only [Real.norm_eq_abs] at h
    rw [h]
    exact hAb
  have hBn : eLpNorm (fun om => c * |B om|) (ENNReal.ofReal (2 * Q)) μ ≤
      ENNReal.ofReal c * ENNReal.ofReal CB := by
    have h := eLpNorm_const_smul_le (c := c) (p := ENNReal.ofReal (2 * Q)) (μ := μ)
      (f := fun om => |B om|)
    rw [Real.enorm_of_nonneg hc] at h
    have hfun : (c • fun om => |B om|) = fun om => c * |B om| := by
      funext om; rfl
    rw [hfun] at h
    refine h.trans (mul_le_mul_right ?_ _)
    have h2 := eLpNorm_norm (p := ENNReal.ofReal (2 * Q)) (μ := μ) (f := B) hB.aestronglyMeasurable
    simp only [Real.norm_eq_abs] at h2
    rw [h2]
    exact hBb
  have hY : eLpNorm (fun om => |A om| + c * |B om|) (ENNReal.ofReal (2 * Q)) μ ≤
      ENNReal.ofReal CA + ENNReal.ofReal c * ENNReal.ofReal CB :=
    (eLpNorm_add_le hp1).trans (add_le_add hAn hBn)
  have hbd : eLpNorm (fun om => RT om * RH om * (|A om| + c * |B om|)) (ENNReal.ofReal Q) μ ≤
      eLpNorm RT (ENNReal.ofReal (2 * (2 * Q))) μ * eLpNorm RH (ENNReal.ofReal (2 * (2 * Q))) μ *
        (ENNReal.ofReal CA + ENNReal.ofReal c * ENNReal.ofReal CB) :=
    (aux_aux_macro_moment_bank_product_moment μ Q _ _ hEs hYs).trans (mul_le_mul' hE hY)
  have hfin : eLpNorm RT (ENNReal.ofReal (2 * (2 * Q))) μ *
      eLpNorm RH (ENNReal.ofReal (2 * (2 * Q))) μ *
        (ENNReal.ofReal CA + ENNReal.ofReal c * ENNReal.ofReal CB) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hRT.eLpNorm_lt_top.ne hRH.eLpNorm_lt_top.ne)
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩)
  exact ⟨lt_of_le_of_lt hbd (lt_top_iff_ne_top.2 hfin), hbd⟩

/-- The truncated global-energy bank: for a finite infrared truncation `H_L` the Dirichlet energy
on a working cube `Q(z,r)`, `r ≤ 1`, is at most `K_N (K_f + C_φ)²` with a random constant of finite
moment of the requested order; the disorder threshold is fixed before the model.  The constant is
the genuine field's coercivity and response constant, transferred by the weight `e^{H_L - H}`. -/
theorem prop_growth_trunc_bank :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (Q : ℝ), 1 ≤ Q →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
    ∀ (L0 : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∃ (Kg : ℕ → BilateralField d → ℝ) (Cg : ℝ),
      (∀ N om, 0 ≤ Kg N om) ∧
      (∀ N, MemLp (Kg N) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure) ∧
      (∀ N, eLpNorm (Kg N) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cg) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet
            (cutoffPositiveCoefficient M (fun om' => infraredPartialSum om' L0) om N z hr) F b u →
          sobolevCoefficientForm
              (cutoffPositiveCoefficient M (fun om' => infraredPartialSum om' L0) om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2 := by
  intro d hd _ _ E P X S Q hQ
  have hQ2 : 1 ≤ 2 * Q := by linarith
  obtain ⟨Cext, hCext, hext⟩ := (lem_extension d hd E X S).1 (3 / 4) ⟨by norm_num, by norm_num⟩
  obtain ⟨dE, hdE, hgrid⟩ := (lem_extension d hd E X S).2 (1 / 8) (2 * Q) (by norm_num) hQ2
    (5 / 8) ⟨by norm_num, by norm_num⟩
  obtain ⟨dc, hdc, hcoer⟩ := aux_lem_coercivity_compat d hd E P S
  refine ⟨min (dc (2 * Q)) dE, lt_min (hdc _ hQ2) hdE, ?_⟩
  intro M Rm hδ L0 z r hr hr1
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  obtain ⟨Kco, hKco, hKmom⟩ := hcoer M Rm H hH z r hr hr1
  obtain ⟨CK, hKmem, hKbd⟩ := hKmom (2 * Q) hQ2 (hδ.trans (min_le_left _ _))
  obtain ⟨K, Cb, hKm, hKb, hae⟩ := hgrid M Rm H hH (hδ.trans (min_le_right _ _)) z 1 one_pos 1
    (fun _ => z)
  have hC0 := aux_aux_macro_moment_bank_Cstar_nonneg d Cext hCext.le
  have hmom := fun N => aux_aux_macro_moment_bank_const_mul_moment (chaosSampleLaw M).toMeasure
    (ENNReal.ofReal (2 * Q)) _ hC0 (K N) Cb (hKm N) (hKb N)
  have hBd := aux_aux_macro_moment_bank_hBd hd E Cext hCext hext M H z r hr hr1 K hae
  have hPc := aux_aux_macro_moment_bank_killed_poincare hd z r hr
  have hRT : MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
      (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure :=
    (aux_prop_growth_trunc_bank_reference hd M L0 (closedCube z r hr) (2 * (2 * Q)) (by linarith)).2.2
  have hRH : MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr)
      (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure :=
    (aux_aux_macro_moment_bank_reference hd M H hH (closedCube z r hr) (2 * (2 * Q))
      (by linarith)).2.2
  have hKgm := fun N => aux_prop_growth_trunc_bank_moment (chaosSampleLaw M).toMeasure Q hQ
    (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
    (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr) hRT hRH
    (fun om => aux_aux_macro_moment_bank_Cstar d Cext * K N om) (Kco N) (aux_prop_growth_trunc_bank_c2 z r hr)
    (aux_prop_growth_trunc_bank_c2_nonneg z r hr) (aux_aux_macro_moment_bank_Cstar d Cext * Cb) CK
    (hmom N).1 (hmom N).2 (hKmem N) (hKbd N)
  obtain ⟨BG, hBG⟩ : ∃ BG : ℝ≥0∞, BG =
      eLpNorm (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
          (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure *
        eLpNorm (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr)
          (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure *
        (ENNReal.ofReal (aux_aux_macro_moment_bank_Cstar d Cext * Cb) +
          ENNReal.ofReal (aux_prop_growth_trunc_bank_c2 z r hr) * ENNReal.ofReal CK) := ⟨_, rfl⟩
  have hBGfin : BG ≠ ⊤ := by
    rw [hBG]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hRT.eLpNorm_lt_top.ne hRH.eLpNorm_lt_top.ne)
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩)
  refine ⟨fun N om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr *
      aux_prop_growth_trunc_bank_refFactor (H om) z r hr *
        (|aux_aux_macro_moment_bank_Cstar d Cext * K N om| + aux_prop_growth_trunc_bank_c2 z r hr * |Kco N om|),
    BG.toReal, ?_, fun N => (hKgm N).1, ?_, ?_⟩
  · intro N om
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (add_nonneg (abs_nonneg _) (mul_nonneg (aux_prop_growth_trunc_bank_c2_nonneg z r hr) (abs_nonneg _)))
  · intro N
    rw [ENNReal.ofReal_toReal hBGfin, hBG]
    exact (hKgm N).2
  · filter_upwards [hBd] with om hom
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    exact aux_prop_growth_trunc_bank_energy_bound hd M H (fun om' => infraredPartialSum om' L0) om N z r hr
      hr1 hPc (Kco N om) (fun v => ((hKco N om).1 v).2) F Kf hKf hFm hFb phi Cphi hphi hCphi b u
      hsolve (aux_aux_macro_moment_bank_Cstar d Cext * K N om)
      (hom N hPc phi Cphi hphi hCphi b hb)

/-- Energy comparison between two infrared fields: on the working cube
`a_H ≤ e^D a_{HT}` when `|HT - H| ≤ D` on `Q̄(z,r)`. -/
theorem aux_prop_growth_trunc_bank_form_transfer {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H HT : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (D : ℝ)
    (hD : ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)), |HT om y - H om y| ≤ D)
    (v : SobolevData (centeredCube z r hr)) :
    sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr) v v ≤
      Real.exp D * sobolevCoefficientForm (cutoffPositiveCoefficient M HT om N z hr) v v := by
  have hmem := ae_restrict_mem (μ := volume) (centeredCube z r hr).isOpen.measurableSet
  have hHae := aux_prop_growth_macro_energy_coeff_ae M H om N z hr
  have hTae := aux_prop_growth_macro_energy_coeff_ae M HT om N z hr
  have hle : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N z hr).val x ≤
        (scalePositiveCoefficient (Real.exp D) (Real.exp_pos D)
          (cutoffPositiveCoefficient M HT om N z hr)).val x := by
    filter_upwards [hHae, hTae, hmem, scalePositiveCoefficient_coeFn (Real.exp D) (Real.exp_pos D)
      (cutoffPositiveCoefficient M HT om N z hr)] with y h1 h2 hy hs
    rw [hs, h1, h2, aux_prop_growth_trunc_bank_ratio M HT H om N y]
    have hpos := cutoffCoefficient_pos M HT om N y
    have hb := hD y (centeredCube_subset_closedCube z hr hy)
    have he : Real.exp (H om y - HT om y) ≤ Real.exp D := by
      refine Real.exp_le_exp.2 ?_
      have := neg_abs_le (HT om y - H om y)
      linarith
    calc cutoffCoefficient M HT om N y * Real.exp (H om y - HT om y)
        ≤ cutoffCoefficient M HT om N y * Real.exp D := mul_le_mul_of_nonneg_left he hpos.le
      _ = Real.exp D * cutoffCoefficient M HT om N y := mul_comm _ _
  have h := sobolevCoefficientForm_mono (cutoffPositiveCoefficient M H om N z hr)
    (scalePositiveCoefficient (Real.exp D) (Real.exp_pos D)
      (cutoffPositiveCoefficient M HT om N z hr)) hle v
  rwa [sobolevCoefficientForm_scale] at h

/-- A random factor in `L^{2P}` has its square in `L^P`. -/
theorem aux_prop_growth_trunc_bank_memLp_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : ℝ)
    (R : Ω → ℝ) (hR : MemLp R (ENNReal.ofReal (2 * P)) μ) :
    MemLp (fun om => R om * R om) (ENNReal.ofReal P) μ :=
  lt_of_le_of_lt (aux_aux_macro_moment_bank_product_moment μ P R R hR.aestronglyMeasurable hR.aestronglyMeasurable)
    (ENNReal.mul_lt_top hR.eLpNorm_lt_top hR.eLpNorm_lt_top)

/-- **The cross bank.**  For a finite infrared truncation `H_L` and the characterized field `H₀`
of the same model, the `H₀`-energy of the `H_L`-Dirichlet solution on a working cube `Q(z,r)`,
`r ≤ 1`, is at most `K_N (K_f + C_φ)²`, with a random constant of finite moment of the requested
order; the disorder threshold is fixed before the model. -/
theorem aux_prop_growth_trunc_bank_cross :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (Q : ℝ), 1 ≤ Q →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
    ∀ (H0 : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H0 →
    ∀ (L0 : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∃ (Kg : ℕ → BilateralField d → ℝ) (Cg : ℝ),
      (∀ N om, 0 ≤ Kg N om) ∧
      (∀ N, MemLp (Kg N) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure) ∧
      (∀ N, eLpNorm (Kg N) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cg) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet
            (cutoffPositiveCoefficient M (fun om' => infraredPartialSum om' L0) om N z hr) F b u →
          sobolevCoefficientForm (cutoffPositiveCoefficient M H0 om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2 := by
  intro d hd _ _ E P X S Q hQ
  have hQ2 : 1 ≤ 2 * Q := by linarith
  obtain ⟨Cext, hCext, hext⟩ := (lem_extension d hd E X S).1 (3 / 4) ⟨by norm_num, by norm_num⟩
  obtain ⟨dE, hdE, hgrid⟩ := (lem_extension d hd E X S).2 (1 / 8) (2 * Q) (by norm_num) hQ2
    (5 / 8) ⟨by norm_num, by norm_num⟩
  obtain ⟨dc, hdc, hcoer⟩ := aux_lem_coercivity_compat d hd E P S
  refine ⟨min (dc (2 * Q)) dE, lt_min (hdc _ hQ2) hdE, ?_⟩
  intro M Rm hδ H hH L0 z r hr hr1
  obtain ⟨Kco, hKco, hKmom⟩ := hcoer M Rm H hH z r hr hr1
  obtain ⟨CK, hKmem, hKbd⟩ := hKmom (2 * Q) hQ2 (hδ.trans (min_le_left _ _))
  obtain ⟨K, Cb, hKm, hKb, hae⟩ := hgrid M Rm H hH (hδ.trans (min_le_right _ _)) z 1 one_pos 1
    (fun _ => z)
  have hC0 := aux_aux_macro_moment_bank_Cstar_nonneg d Cext hCext.le
  have hmom := fun N => aux_aux_macro_moment_bank_const_mul_moment (chaosSampleLaw M).toMeasure
    (ENNReal.ofReal (2 * Q)) _ hC0 (K N) Cb (hKm N) (hKb N)
  have hBd := aux_aux_macro_moment_bank_hBd hd E Cext hCext hext M H z r hr hr1 K hae
  have hPc := aux_aux_macro_moment_bank_killed_poincare hd z r hr
  have hRT : MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr *
        aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
      (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure :=
    aux_prop_growth_trunc_bank_memLp_sq _ _ _
      (aux_prop_growth_trunc_bank_reference hd M L0 (closedCube z r hr) (2 * (2 * (2 * Q)))
        (by linarith)).2.2
  have hRH : MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr *
        aux_prop_growth_trunc_bank_refFactor (H om) z r hr)
      (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure :=
    aux_prop_growth_trunc_bank_memLp_sq _ _ _
      (aux_aux_macro_moment_bank_reference hd M H hH (closedCube z r hr) (2 * (2 * (2 * Q)))
        (by linarith)).2.2
  have hKgm := fun N => aux_prop_growth_trunc_bank_moment (chaosSampleLaw M).toMeasure Q hQ
    (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr *
      aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
    (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr * aux_prop_growth_trunc_bank_refFactor (H om) z r hr) hRT hRH
    (fun om => aux_aux_macro_moment_bank_Cstar d Cext * K N om) (Kco N) (aux_prop_growth_trunc_bank_c2 z r hr)
    (aux_prop_growth_trunc_bank_c2_nonneg z r hr) (aux_aux_macro_moment_bank_Cstar d Cext * Cb) CK
    (hmom N).1 (hmom N).2 (hKmem N) (hKbd N)
  obtain ⟨BG, hBG⟩ : ∃ BG : ℝ≥0∞, BG =
      eLpNorm (fun om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr *
          aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr)
          (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure *
        eLpNorm (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z r hr * aux_prop_growth_trunc_bank_refFactor (H om) z r hr)
          (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure *
        (ENNReal.ofReal (aux_aux_macro_moment_bank_Cstar d Cext * Cb) +
          ENNReal.ofReal (aux_prop_growth_trunc_bank_c2 z r hr) * ENNReal.ofReal CK) := ⟨_, rfl⟩
  have hBGfin : BG ≠ ⊤ := by
    rw [hBG]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hRT.eLpNorm_lt_top.ne hRH.eLpNorm_lt_top.ne)
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩)
  refine ⟨fun N om => aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr *
      aux_prop_growth_trunc_bank_refFactor (infraredPartialSum om L0) z r hr *
      (aux_prop_growth_trunc_bank_refFactor (H om) z r hr * aux_prop_growth_trunc_bank_refFactor (H om) z r hr) *
        (|aux_aux_macro_moment_bank_Cstar d Cext * K N om| + aux_prop_growth_trunc_bank_c2 z r hr * |Kco N om|),
    BG.toReal, ?_, fun N => (hKgm N).1, ?_, ?_⟩
  · intro N om
    have h1 := (Real.exp_pos
      ‖(infraredPartialSum om L0).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖).le
    have h2 := (Real.exp_pos
      ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖).le
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h1) (mul_nonneg h2 h2))
      (add_nonneg (abs_nonneg _) (mul_nonneg (aux_prop_growth_trunc_bank_c2_nonneg z r hr) (abs_nonneg _)))
  · intro N
    rw [ENNReal.ofReal_toReal hBGfin, hBG]
    exact (hKgm N).2
  · filter_upwards [hBd] with om hom
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have hT := aux_prop_growth_trunc_bank_energy_bound hd M H (fun om' => infraredPartialSum om' L0) om N z r
      hr hr1 hPc (Kco N om) (fun v => ((hKco N om).1 v).2) F Kf hKf hFm hFb phi Cphi hphi hCphi b u
      hsolve (aux_aux_macro_moment_bank_Cstar d Cext * K N om)
      (hom N hPc phi Cphi hphi hCphi b hb)
    have hX := aux_prop_growth_trunc_bank_form_transfer M H (fun om' => infraredPartialSum om' L0) om N z r hr
      (‖(infraredPartialSum om L0).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ +
        ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖)
      (aux_prop_growth_trunc_bank_diff_le (infraredPartialSum om L0) (H om) z r hr)
      (u : SobolevData (centeredCube z r hr))
    refine hX.trans ((mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le).trans (le_of_eq ?_))
    unfold aux_prop_growth_trunc_bank_refFactor
    rw [Real.exp_add]
    ring

end Paper
