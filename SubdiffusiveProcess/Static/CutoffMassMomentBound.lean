module

public import SubdiffusiveProcess.Static.CutoffCubeMoments
public import SubdiffusiveProcess.Analysis.RawLp
public import SubdiffusiveProcess.Section9.CutoffLogTail
public import SubdiffusiveProcess.CoarseGrainingVocab.DeltaLogSquaredTail

@[expose] public section

/-! # Uniform two-sided mass moments above the finite cutoff

The Section 9 logarithmic tail supplies the matching-scale moments.
Normalized spatial averaging then extends them to every larger cube.
-/

open MeasureTheory ProbabilityTheory Homogenization SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Conversion between a nonnegative real moment and its `Lᵖ` seminorm. -/
theorem lintegral_rpow_eq_eLpNorm_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) {q : ℝ} (hq : 0 < q) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ) = SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal q) μ ^ q := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by simpa using hq) ENNReal.ofReal_ne_top f μ,
    ENNReal.toReal_ofReal hq.le, one_div, ENNReal.rpow_inv_rpow hq.ne']
  apply lintegral_congr
  intro ω
  rw [Real.enorm_eq_ofReal (hf ω), ENNReal.ofReal_rpow_of_nonneg (hf ω) hq.le]



theorem lintegral_rpow_eq_eLpNorm_rpow_of_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {q : ℝ} (hq : 0 < q) (hfm : AEStronglyMeasurable f μ) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ) = eLpNorm f (ENNReal.ofReal q) μ ^ q := by
  rw [lintegral_rpow_eq_eLpNorm_rpow μ f hf hq, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hfm]

/-- The logarithmic tail controls both signs of a mass moment at once. -/
theorem mass_moments_le_of_logAbs_ogamma {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → ℝ) (hV : ∀ ω, 0 < V ω)
    {A q : ℝ} (hA : 0 < A) (hq : 0 < q) (hqa : q * A ≤ 1)
    (hX : SubdiffusiveProcess.OGammaLE μ 1 A (fun ω => |Real.log (V ω)| - Real.log 2)) :
    (∫⁻ ω, ENNReal.ofReal (V ω ^ q) ∂μ) ≤ ENNReal.ofReal ((2 : ℝ) ^ q * 2) ∧
      (∫⁻ ω, ENNReal.ofReal ((V ω)⁻¹ ^ q) ∂μ) ≤ ENNReal.ofReal ((2 : ℝ) ^ q * 2) := by
  let G : Ω → ℝ := fun ω => Real.exp (A⁻¹ * max (|Real.log (V ω)| - Real.log 2) 0)
  have hGi : Integrable G μ := by
    simpa only [G, SubdiffusiveProcess.OGammaLE, Real.rpow_one] using hX.1
  have hGb : (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ) ≤ 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hGi
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    have h := ENNReal.ofReal_le_ofReal hX.2
    simpa only [G, Real.rpow_one, ENNReal.ofReal_ofNat] using h
  have hqA : q ≤ A⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hA).mpr hqa
  have hpoint : ∀ ω, V ω ^ q ≤ (2 : ℝ) ^ q * G ω ∧
      (V ω)⁻¹ ^ q ≤ (2 : ℝ) ^ q * G ω := by
    intro ω
    have hexp : Real.exp (q * |Real.log (V ω)|) ≤ (2 : ℝ) ^ q * G ω := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm : 0 ≤ max (|Real.log (V ω)| - Real.log 2) 0 := le_max_right _ _
      have hml := le_max_left (|Real.log (V ω)| - Real.log 2) 0
      nlinarith
    constructor
    · apply le_trans _ hexp
      rw [Real.rpow_def_of_pos (hV ω)]
      apply Real.exp_le_exp.mpr
      nlinarith only [le_abs_self (Real.log (V ω)), hq]
    · apply le_trans _ hexp
      rw [Real.rpow_def_of_pos (inv_pos.mpr (hV ω)), Real.log_inv]
      apply Real.exp_le_exp.mpr
      nlinarith only [neg_le_abs (Real.log (V ω)), hq]
  have hbound : ∀ (F : Ω → ℝ), (∀ ω, F ω ≤ (2 : ℝ) ^ q * G ω) →
      (∫⁻ ω, ENNReal.ofReal (F ω) ∂μ) ≤ ENNReal.ofReal ((2 : ℝ) ^ q * 2) := by
    intro F hF
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) ^ q * G ω) ∂μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hF ω)
      _ = ENNReal.ofReal ((2 : ℝ) ^ q) * ∫⁻ ω, ENNReal.ofReal (G ω) ∂μ := by
        simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ q) * 2 := mul_le_mul_right hGb _
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q)]
        norm_num
  exact ⟨hbound _ (fun ω => (hpoint ω).1), hbound _ (fun ω => (hpoint ω).2)⟩

/-- A disorder threshold for a prescribed logarithmic-tail moment. -/
theorem exists_log_square_moment_threshold (q C : ℝ) (hq : 0 < q) (hC : 0 < C) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      q * (C * δ ^ 2 * |Real.log δ| ^ 2) ≤ 1 := by
  obtain ⟨δ0, hδ0, _, hcal⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.exists_smallDelta_mul_abs_log_le
      (eps := (q * C + 1)⁻¹) (by positivity)
  refine ⟨δ0, hδ0, ?_⟩
  intro δ hδ hle
  have hc := hcal δ hδ hle
  have hsq : (δ * |Real.log δ|) ^ 2 ≤ ((q * C + 1)⁻¹) ^ 2 := by
    have hnn : 0 ≤ δ * |Real.log δ| := by positivity
    nlinarith [sq_nonneg (δ * |Real.log δ| - (q * C + 1)⁻¹)]
  have hb : (q * C) * ((q * C + 1)⁻¹) ^ 2 ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (q * C)]
  calc
    q * (C * δ ^ 2 * |Real.log δ| ^ 2) = (q * C) * (δ * |Real.log δ|) ^ 2 := by ring
    _ ≤ (q * C) * ((q * C + 1)⁻¹) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ 1 := hb

/-- One deterministic bound controls both signs of the normalized mass
moments, uniformly over finite cutoffs and all larger triadic cubes. -/
theorem exists_uniform_cutoffCube_mass_moments (d : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 →
        ∀ (L k : ℕ), L ≤ k → ∀ Q : TriadicCube d, Q.scale = (k : ℤ) →
          (∫⁻ ω, ENNReal.ofReal (SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω ^ q)
            ∂M.P.toMeasure) ≤ ENNReal.ofReal C ∧
          (∫⁻ ω, ENNReal.ofReal ((SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω)⁻¹ ^ q)
            ∂M.P.toMeasure) ≤ ENNReal.ofReal C := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨Ct, δt, hCt, hδt, ht⟩ := SubdiffusiveProcess.Section9.exists_cutoffOriginCube_logAbs_ogamma d
  obtain ⟨δs, hδs, hs⟩ := exists_log_square_moment_threshold q Ct hq0 hCt
  refine ⟨min δt δs, (2 : ℝ) ^ q * 2, lt_min hδt hδs, by positivity, ?_⟩
  intro M hM L k hLk Q hQ
  have hlog : Real.log M.delta ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one M.shellPrefix.delta_pos
      (ne_of_lt (lt_of_le_of_lt M.shellPrefix.delta_le_half (by norm_num)))
  have hA : 0 < Ct * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    have hδ := M.shellPrefix.delta_pos
    positivity
  obtain ⟨hb, hi⟩ := mass_moments_le_of_logAbs_ogamma M.P.toMeasure
    (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M L)
    (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M L) hA hq0
    (hs M.delta M.shellPrefix.delta_pos (hM.trans (min_le_right _ _)))
    (ht M (hM.trans (min_le_left _ _)) L)
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  constructor
  · rw [lintegral_rpow_eq_eLpNorm_rpow_of_aestronglyMeasurable _ _ (fun ω => (cutoffCubeAverage_pos M L Q ω).le) hq0
      (SubdiffusiveProcess.Section9.measurable_cutoffCubeAverage M L Q).aestronglyMeasurable]
    apply le_trans (ENNReal.rpow_le_rpow
      (eLpNorm_cutoffCubeAverage_le_origin M hLk Q hQ _ hp) hq0.le)
    rwa [← lintegral_rpow_eq_eLpNorm_rpow_of_aestronglyMeasurable _ _
      (fun ω => (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M L ω).le) hq0
      (SubdiffusiveProcess.Section9.measurable_cutoffOriginCubeAverage M L).aestronglyMeasurable]
  · rw [lintegral_rpow_eq_eLpNorm_rpow_of_aestronglyMeasurable _ _
      (fun ω => inv_nonneg.mpr (cutoffCubeAverage_pos M L Q ω).le) hq0
      (SubdiffusiveProcess.Section9.measurable_cutoffCubeAverage M L Q).inv.aestronglyMeasurable]
    apply le_trans (ENNReal.rpow_le_rpow
      (eLpNorm_inverse_cutoffCubeAverage_le_origin M hLk Q hQ _ hp) hq0.le)
    rwa [← lintegral_rpow_eq_eLpNorm_rpow_of_aestronglyMeasurable _ _
      (fun ω => inv_nonneg.mpr (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M L ω).le) hq0
      (SubdiffusiveProcess.Section9.measurable_cutoffOriginCubeAverage M L).inv.aestronglyMeasurable]

end SubdiffusiveProcess.Static
