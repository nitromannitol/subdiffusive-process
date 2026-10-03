module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452Reversal
public import SubdiffusiveProcess.Probability.Diffusion.Packet452DynkinDoob

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- **Doob's `L²` maximal inequality in continuous time, for any continuous martingale on path
space.** -/
theorem lintegral_iSup_sq_martingale_le {μ : Measure (ContinuousPath (Vec d))}
    [IsFiniteMeasure μ] {M : ℝ≥0 → ContinuousPath (Vec d) → ℝ}
    (hmart : Martingale M (ContinuousPath.canonicalFiltration (alpha := Vec d)) μ)
    (hcont : ∀ ω, Continuous fun t : ℝ≥0 => M t ω)
    (hmeas : ∀ t : ℝ≥0, Measurable (M t)) (T : ℝ≥0) :
    (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((M t ω) ^ 2)) ∂μ)
      ≤ 4 * ∫⁻ ω, ENNReal.ofReal ((M T ω) ^ 2) ∂μ := by
  classical
  have hFcont : ∀ ω : ContinuousPath (Vec d),
      Continuous fun t : ℝ≥0 => ENNReal.ofReal ((M t ω) ^ 2) := fun ω =>
    ENNReal.continuous_ofReal.comp ((hcont ω).pow 2)
  have hslice : ∀ t : ℝ≥0, Measurable fun ω : ContinuousPath (Vec d) =>
      ENNReal.ofReal ((M t ω) ^ 2) := fun t => ((hmeas t).pow_const 2).ennreal_ofReal
  have hgm : ∀ n : ℕ, Measurable fun ω : ContinuousPath (Vec d) =>
      dyadicGridSup (fun t : ℝ≥0 => ENNReal.ofReal ((M t ω) ^ 2)) T n := by
    intro n
    exact Finset.measurable_range_sup'' (f := fun k ω =>
      ENNReal.ofReal ((M (dyadicTime T n k) ω) ^ 2)) (fun k _ => hslice (dyadicTime T n k))
  refine le_trans (lintegral_iSup_le_dyadicGridSup hFcont hgm) (iSup_le fun n => ?_)
  have hgrid := lintegral_sq_sup_abs_le hmart (dyadicTime T n) (monotone_dyadicTime T n) (2 ^ n)
  simp only [dyadicTime_last] at hgrid
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hgrid
  exact (ofReal_sq_sup' Finset.nonempty_range_add_one
    (fun k => M (dyadicTime T n k) ω)).symm

/-- **The Dynkin increment is a martingale.** -/
theorem martingale_dynkin_increment
    (f : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain) (x : Vec d) :
    Martingale (fun t ω => isFeller_laplacianSemigroup.dynkinProcess f t ω
        - isFeller_laplacianSemigroup.dynkinProcess f 0 ω)
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (laplacianContinuousLaw d x) := by
  have hmart : Martingale (isFeller_laplacianSemigroup.dynkinProcess f)
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (laplacianContinuousLaw d x) :=
    isFeller_laplacianSemigroup.martingale_dynkinProcess isConservative_laplacianSemigroup
      kolmogorovRegular_laplacianSemigroup f x
  have hconst : Martingale
      (fun _ : ℝ≥0 => isFeller_laplacianSemigroup.dynkinProcess f 0)
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (laplacianContinuousLaw d x) :=
    martingale_const_fun _ _
      (isFeller_laplacianSemigroup.stronglyMeasurable_dynkinProcess_canonicalFiltration f 0)
      (isFeller_laplacianSemigroup.integrable_dynkinProcess isConservative_laplacianSemigroup f 0 x)
  exact hmart.sub hconst

/-! ## Integrability of the terminal second moment in `x` -/

theorem integrable_x_sq_eval_time (f : C₀(Vec d, ℝ))
    (hfsupp : HasCompactSupport (f : Vec d → ℝ)) {T : ℝ≥0} (hT : 0 < (T : ℝ)) :
    Integrable (fun x => ∫ ω, ((f : Vec d → ℝ) (ω T)) ^ 2
      ∂(laplacianContinuousLaw d x)) volume := by
  have hcoe : ((f * f : C₀(Vec d, ℝ)) : Vec d → ℝ) = (f : Vec d → ℝ) * (f : Vec d → ℝ) :=
    ZeroAtInftyContinuousMap.coe_mul f f
  have hsupp : HasCompactSupport ((f * f : C₀(Vec d, ℝ)) : Vec d → ℝ) := by
    rw [hcoe]; exact hfsupp.mul_right
  have hint : Integrable ((f * f : C₀(Vec d, ℝ)) : Vec d → ℝ) :=
    (map_continuous _).integrable_of_hasCompactSupport hsupp
  have hnn : ∀ z, 0 ≤ ((f * f : C₀(Vec d, ℝ)) : Vec d → ℝ) z := by
    intro z; rw [hcoe]; exact mul_self_nonneg _
  have h := integrable_semigroup_apply (t := (T : ℝ)) hT (f * f) hnn hint
  rw [Real.toNNReal_coe] at h
  exact h.congr (Eventually.of_forall fun x => (integral_path_sq_eval f T x).symm)

theorem integrable_x_sq_eval_zero (f : C₀(Vec d, ℝ))
    (hfsupp : HasCompactSupport (f : Vec d → ℝ)) :
    Integrable (fun x => ∫ ω, ((f : Vec d → ℝ) (ω 0)) ^ 2
      ∂(laplacianContinuousLaw d x)) volume := by
  have hcoe : ((f * f : C₀(Vec d, ℝ)) : Vec d → ℝ) = (f : Vec d → ℝ) * (f : Vec d → ℝ) :=
    ZeroAtInftyContinuousMap.coe_mul f f
  have hsupp : HasCompactSupport ((f * f : C₀(Vec d, ℝ)) : Vec d → ℝ) := by
    rw [hcoe]; exact hfsupp.mul_right
  have hint : Integrable ((f * f : C₀(Vec d, ℝ)) : Vec d → ℝ) :=
    (map_continuous _).integrable_of_hasCompactSupport hsupp
  refine hint.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [integral_path_sq_eval f 0 x, brownianSemigroup_zero]

theorem integrable_x_sq_timeIntegralPath (g : C₀(Vec d, ℝ))
    (hgsupp : HasCompactSupport (g : Vec d → ℝ)) (T : ℝ≥0) :
    Integrable (fun x => ∫ ω, (timeIntegralPath g T ω) ^ 2
      ∂(laplacianContinuousLaw d x)) volume := by
  have hCsm : StronglyMeasurable (timeIntegralPath g T) := stronglyMeasurable_timeIntegralPath g T
  have hCb : ∀ ω, |timeIntegralPath g T ω| ≤ ‖g‖ * (T : ℝ) := abs_timeIntegralPath_le g T
  have hugint : Integrable ((absC0 g hgsupp : C₀(Vec d, ℝ)) : Vec d → ℝ) :=
    (map_continuous _).integrable_of_hasCompactSupport (hasCompactSupport_absC0 g hgsupp)
  refine integrable_pathIntegral_of_le (hCsm.pow 2)
    ((integrable_timeIntegral_semigroup T (absC0 g hgsupp) (absC0_nonneg g hgsupp)
      hugint).const_mul (‖g‖ * (T : ℝ))) fun x => ?_
  have hmaj : Integrable (fun ω => (‖g‖ * (T : ℝ)) * timeIntegralPath (absC0 g hgsupp) T ω)
      (laplacianContinuousLaw d x) :=
    (Integrable.of_bound
      (stronglyMeasurable_timeIntegralPath (absC0 g hgsupp) T).aestronglyMeasurable
      (‖absC0 g hgsupp‖ * (T : ℝ)) (Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using abs_timeIntegralPath_le (absC0 g hgsupp) T ω)).const_mul _
  have hint2 : Integrable (fun ω => (timeIntegralPath g T ω) ^ 2)
      (laplacianContinuousLaw d x) :=
    Integrable.of_bound (hCsm.pow 2).aestronglyMeasurable ((‖g‖ * (T : ℝ)) ^ 2)
      (Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using
          (abs_pow (timeIntegralPath g T ω) 2).trans_le
            (pow_le_pow_left₀ (abs_nonneg _) (hCb ω) 2))
  calc ‖∫ ω, (timeIntegralPath g T ω) ^ 2 ∂(laplacianContinuousLaw d x)‖
      ≤ ∫ ω, ‖(timeIntegralPath g T ω) ^ 2‖ ∂(laplacianContinuousLaw d x) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (‖g‖ * (T : ℝ)) * timeIntegralPath (absC0 g hgsupp) T ω
          ∂(laplacianContinuousLaw d x) := by
        refine integral_mono hint2.norm hmaj fun ω => ?_
        have h1 : ‖(timeIntegralPath g T ω) ^ 2‖
            = |timeIntegralPath g T ω| * |timeIntegralPath g T ω| := by
          rw [Real.norm_eq_abs, abs_pow]; ring
        rw [h1]
        exact mul_le_mul (hCb ω) (abs_timeIntegralPath_le_abs g hgsupp T ω) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hCb ω))
    _ = (‖g‖ * (T : ℝ)) * ∫ t in (0 : ℝ)..(T : ℝ),
          (brownianSemigroup d) (Real.toNNReal t) (absC0 g hgsupp) x := by
        rw [integral_const_mul, integral_path_timeIntegral (absC0 g hgsupp) T x]

theorem integrable_sq_dynkin_increment_path (f g : C₀(Vec d, ℝ)) (T : ℝ≥0) (x : Vec d) :
    Integrable (fun ω => ((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
      - timeIntegralPath g T ω) ^ 2) (laplacianContinuousLaw d x) := by
  have hAsm : StronglyMeasurable fun ω : ContinuousPath (Vec d) => (f : Vec d → ℝ) (ω T) :=
    (map_continuous f).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess T).stronglyMeasurable
  have hBsm : StronglyMeasurable fun ω : ContinuousPath (Vec d) => (f : Vec d → ℝ) (ω 0) :=
    (map_continuous f).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess 0).stronglyMeasurable
  have hCsm : StronglyMeasurable (timeIntegralPath g T) := stronglyMeasurable_timeIntegralPath g T
  refine Integrable.of_bound (((hAsm.sub hBsm).sub hCsm).pow 2).aestronglyMeasurable
    ((‖f‖ + ‖f‖ + ‖g‖ * (T : ℝ)) ^ 2) (Eventually.of_forall fun ω => ?_)
  have hb : |(f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g T ω|
      ≤ ‖f‖ + ‖f‖ + ‖g‖ * (T : ℝ) := by
    refine (abs_sub _ _).trans ?_
    exact add_le_add ((abs_sub _ _).trans
      (add_le_add (abs_c0_apply_le f _) (abs_c0_apply_le f _)))
      (abs_timeIntegralPath_le g T ω)
  simpa [Real.norm_eq_abs] using
    (abs_pow _ 2).trans_le (pow_le_pow_left₀ (abs_nonneg _) hb 2)

/-- The terminal second moment is integrable in `x`. -/
theorem integrable_x_sq_dynkin_increment (f g : C₀(Vec d, ℝ))
    (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgsupp : HasCompactSupport (g : Vec d → ℝ)) {T : ℝ≥0} (hT : 0 < (T : ℝ)) :
    Integrable (fun x => ∫ ω, ((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
      - timeIntegralPath g T ω) ^ 2 ∂(laplacianContinuousLaw d x)) volume := by
  have hAsm : StronglyMeasurable fun ω : ContinuousPath (Vec d) => (f : Vec d → ℝ) (ω T) :=
    (map_continuous f).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess T).stronglyMeasurable
  have hBsm : StronglyMeasurable fun ω : ContinuousPath (Vec d) => (f : Vec d → ℝ) (ω 0) :=
    (map_continuous f).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess 0).stronglyMeasurable
  have hCsm : StronglyMeasurable (timeIntegralPath g T) := stronglyMeasurable_timeIntegralPath g T
  have hAb : ∀ ω : ContinuousPath (Vec d), |(f : Vec d → ℝ) (ω T)| ≤ ‖f‖ :=
    fun ω => abs_c0_apply_le f _
  have hBb : ∀ ω : ContinuousPath (Vec d), |(f : Vec d → ℝ) (ω 0)| ≤ ‖f‖ :=
    fun ω => abs_c0_apply_le f _
  have hCb : ∀ ω, |timeIntegralPath g T ω| ≤ ‖g‖ * (T : ℝ) := abs_timeIntegralPath_le g T
  refine integrable_pathIntegral_of_le
    (((hAsm.sub hBsm).sub hCsm).pow 2)
    ((((integrable_x_sq_eval_time f hfsupp hT).add (integrable_x_sq_eval_zero f hfsupp)).add
      (integrable_x_sq_timeIntegralPath g hgsupp T)).const_mul 3) fun x => ?_
  have hmeasA : Integrable (fun ω : ContinuousPath (Vec d) => ((f : Vec d → ℝ) (ω T)) ^ 2)
      (laplacianContinuousLaw d x) :=
    Integrable.of_bound (hAsm.pow 2).aestronglyMeasurable (‖f‖ ^ 2)
      (Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using
          (abs_pow ((f : Vec d → ℝ) (ω T)) 2).trans_le
            (pow_le_pow_left₀ (abs_nonneg _) (hAb ω) 2))
  have hmeasB : Integrable (fun ω : ContinuousPath (Vec d) => ((f : Vec d → ℝ) (ω 0)) ^ 2)
      (laplacianContinuousLaw d x) :=
    Integrable.of_bound (hBsm.pow 2).aestronglyMeasurable (‖f‖ ^ 2)
      (Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using
          (abs_pow ((f : Vec d → ℝ) (ω 0)) 2).trans_le
            (pow_le_pow_left₀ (abs_nonneg _) (hBb ω) 2))
  have hmeasC : Integrable (fun ω => (timeIntegralPath g T ω) ^ 2)
      (laplacianContinuousLaw d x) :=
    Integrable.of_bound (hCsm.pow 2).aestronglyMeasurable ((‖g‖ * (T : ℝ)) ^ 2)
      (Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using
          (abs_pow (timeIntegralPath g T ω) 2).trans_le
            (pow_le_pow_left₀ (abs_nonneg _) (hCb ω) 2))
  have hmeasM : Integrable (fun ω : ContinuousPath (Vec d) =>
      ((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g T ω) ^ 2)
      (laplacianContinuousLaw d x) :=
    Integrable.of_bound (((hAsm.sub hBsm).sub hCsm).pow 2).aestronglyMeasurable
      ((‖f‖ + ‖f‖ + ‖g‖ * (T : ℝ)) ^ 2)
      (Eventually.of_forall fun ω => by
        have hb : |(f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g T ω|
            ≤ ‖f‖ + ‖f‖ + ‖g‖ * (T : ℝ) := by
          refine (abs_sub _ _).trans ?_
          exact add_le_add ((abs_sub _ _).trans (add_le_add (hAb ω) (hBb ω))) (hCb ω)
        simpa [Real.norm_eq_abs] using
          (abs_pow _ 2).trans_le (pow_le_pow_left₀ (abs_nonneg _) hb 2))
  have hmeasAB : Integrable (fun ω : ContinuousPath (Vec d) =>
      ((f : Vec d → ℝ) (ω T)) ^ 2 + ((f : Vec d → ℝ) (ω 0)) ^ 2)
      (laplacianContinuousLaw d x) := hmeasA.add hmeasB
  have hmeasABC : Integrable (fun ω : ContinuousPath (Vec d) =>
      ((f : Vec d → ℝ) (ω T)) ^ 2 + ((f : Vec d → ℝ) (ω 0)) ^ 2
        + (timeIntegralPath g T ω) ^ 2) (laplacianContinuousLaw d x) := hmeasAB.add hmeasC
  have hmaj : Integrable (fun ω : ContinuousPath (Vec d) =>
      3 * (((f : Vec d → ℝ) (ω T)) ^ 2 + ((f : Vec d → ℝ) (ω 0)) ^ 2
        + (timeIntegralPath g T ω) ^ 2)) (laplacianContinuousLaw d x) := hmeasABC.const_mul 3
  calc ‖∫ ω, ((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g T ω) ^ 2
        ∂(laplacianContinuousLaw d x)‖
      ≤ ∫ ω, ‖((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g T ω) ^ 2‖
          ∂(laplacianContinuousLaw d x) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 3 * (((f : Vec d → ℝ) (ω T)) ^ 2 + ((f : Vec d → ℝ) (ω 0)) ^ 2
          + (timeIntegralPath g T ω) ^ 2) ∂(laplacianContinuousLaw d x) := by
        refine integral_mono hmeasM.norm hmaj fun ω => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg ((f : Vec d → ℝ) (ω T) + (f : Vec d → ℝ) (ω 0)),
          sq_nonneg ((f : Vec d → ℝ) (ω T) + timeIntegralPath g T ω),
          sq_nonneg ((f : Vec d → ℝ) (ω 0) - timeIntegralPath g T ω)]
    _ = 3 * ((∫ ω, ((f : Vec d → ℝ) (ω T)) ^ 2 ∂(laplacianContinuousLaw d x))
          + (∫ ω, ((f : Vec d → ℝ) (ω 0)) ^ 2 ∂(laplacianContinuousLaw d x))
          + ∫ ω, (timeIntegralPath g T ω) ^ 2 ∂(laplacianContinuousLaw d x)) := by
        rw [integral_const_mul, integral_add hmeasAB hmeasC, integral_add hmeasA hmeasB]

/-! ## The forward maximal bound -/

theorem dynkinProcess_eq_sub_timeIntegralPath (f g : C₀(Vec d, ℝ))
    (hf2 : ContDiff ℝ 2 (f : Vec d → ℝ)) (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    (t : ℝ≥0) (ω : ContinuousPath (Vec d)) :
    isFeller_laplacianSemigroup.dynkinProcess
        ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩ t ω
      = (f : Vec d → ℝ) (ω t) - timeIntegralPath g t ω := by
  rw [SubMarkovKernelSemigroup.IsFellerKernelSemigroup.dynkinProcess_apply,
    generator_laplacianSemigroup f g hf2 hfsupp hgdef]
  rfl

/-- The terminal second moment, in `ℝ≥0∞`: §2's value read through `ENNReal.ofReal`. -/
theorem lintegral_x_sq_dynkin_increment (f g : C₀(Vec d, ℝ))
    (hf2 : ContDiff ℝ 2 (f : Vec d → ℝ)) (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgsupp : HasCompactSupport (g : Vec d → ℝ))
    (hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    {T : ℝ≥0} (hT : 0 < (T : ℝ)) :
    (∫⁻ x, (∫⁻ ω, ENNReal.ofReal (((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
        - timeIntegralPath g T ω) ^ 2) ∂(laplacianContinuousLaw d x)) ∂volume)
      = ENNReal.ofReal (-2 * (T : ℝ) * ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume) := by
  have hinner : ∀ x : Vec d,
      (∫⁻ ω, ENNReal.ofReal (((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
          - timeIntegralPath g T ω) ^ 2) ∂(laplacianContinuousLaw d x))
        = ENNReal.ofReal (∫ ω, ((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
          - timeIntegralPath g T ω) ^ 2 ∂(laplacianContinuousLaw d x)) := fun x =>
    (ofReal_integral_eq_lintegral_ofReal (integrable_sq_dynkin_increment_path f g T x)
      (Eventually.of_forall fun ω => sq_nonneg _)).symm
  simp only [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_x_sq_dynkin_increment f g hfsupp hgsupp hT)
    (Eventually.of_forall fun x => integral_nonneg fun ω => sq_nonneg _),
    integral_x_sq_dynkin_increment f g hf2 hfsupp hgsupp hgdef hT]

/-- **§3's forward conclusion**: `∫ₓ E_x[sup_{t ≤ T} M_t²] dx ≤ 8T·E(φ)`. -/
theorem lintegral_x_iSup_sq_dynkin_increment_le (f g : C₀(Vec d, ℝ))
    (hf2 : ContDiff ℝ 2 (f : Vec d → ℝ)) (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgsupp : HasCompactSupport (g : Vec d → ℝ))
    (hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    {T : ℝ≥0} (hT : 0 < (T : ℝ)) :
    (∫⁻ x, (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal
        (((f : Vec d → ℝ) (ω t) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g t ω) ^ 2))
        ∂(laplacianContinuousLaw d x)) ∂volume)
      ≤ ENNReal.ofReal (8 * (T : ℝ) * (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)) := by
  set F : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain :=
    ⟨f, mem_generatorDomain_laplacianSemigroup f g hf2 hfsupp hgdef⟩ with hF
  have hrw : ∀ (t : ℝ≥0) (ω : ContinuousPath (Vec d)),
      isFeller_laplacianSemigroup.dynkinProcess F t ω
        - isFeller_laplacianSemigroup.dynkinProcess F 0 ω
      = (f : Vec d → ℝ) (ω t) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g t ω := by
    intro t ω
    rw [hF, dynkinProcess_eq_sub_timeIntegralPath f g hf2 hfsupp hgdef t ω,
      dynkinProcess_eq_sub_timeIntegralPath f g hf2 hfsupp hgdef 0 ω]
    have h0 : timeIntegralPath g 0 ω = 0 := by
      simp [timeIntegralPath]
    rw [h0]
    ring
  have hpx : ∀ x : Vec d,
      (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal
          (((f : Vec d → ℝ) (ω t) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g t ω) ^ 2))
          ∂(laplacianContinuousLaw d x))
        ≤ 4 * ∫⁻ ω, ENNReal.ofReal (((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
          - timeIntegralPath g T ω) ^ 2) ∂(laplacianContinuousLaw d x) := by
    intro x
    have h := lintegral_iSup_sq_martingale_le (martingale_dynkin_increment F x)
      (fun ω => (isFeller_laplacianSemigroup.continuous_dynkinProcess F ω).sub continuous_const)
      (fun t => (isFeller_laplacianSemigroup.stronglyMeasurable_dynkinProcess F t).measurable.sub
        (isFeller_laplacianSemigroup.stronglyMeasurable_dynkinProcess F 0).measurable) T
    simpa only [hrw] using h
  calc (∫⁻ x, (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal
        (((f : Vec d → ℝ) (ω t) - (f : Vec d → ℝ) (ω 0) - timeIntegralPath g t ω) ^ 2))
        ∂(laplacianContinuousLaw d x)) ∂volume)
      ≤ ∫⁻ x, 4 * (∫⁻ ω, ENNReal.ofReal (((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
          - timeIntegralPath g T ω) ^ 2) ∂(laplacianContinuousLaw d x)) ∂volume :=
        lintegral_mono hpx
    _ = 4 * ∫⁻ x, (∫⁻ ω, ENNReal.ofReal (((f : Vec d → ℝ) (ω T) - (f : Vec d → ℝ) (ω 0)
          - timeIntegralPath g T ω) ^ 2) ∂(laplacianContinuousLaw d x)) ∂volume :=
        lintegral_const_mul' 4 _ (by norm_num)
    _ = 4 * ENNReal.ofReal (-2 * (T : ℝ) *
          ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume) := by
        rw [lintegral_x_sq_dynkin_increment f g hf2 hfsupp hgsupp hgdef hT]
    _ = ENNReal.ofReal (8 * (T : ℝ) *
          (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)) := by
        rw [show (8 : ℝ) * (T : ℝ) * (- ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume)
            = 4 * (-2 * (T : ℝ) * ∫ y, (f : Vec d → ℝ) y * (g : Vec d → ℝ) y ∂volume) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
