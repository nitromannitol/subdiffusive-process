module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.UniformLimit

@[expose] public section

/-!
# A.e. limits from `L¹` control, and sequence independence

Sequence independence follows from two reusable facts:

* `ae_tendsto_zero_of_tsum_lintegral_ne_top` — summable integrals force a.e. convergence to `0`.
  Same Tonelli-plus-`ae_lt_top'` mechanism as `ae_tsum_lt_top_of_lintegral_sq`, again with **no**
  finiteness assumption on `μ`.
* `exists_subseq_ae_tendsto_zero` — the `L¹`-to-a.e. extraction: convergence of the integrals to
  `0` gives a strictly monotone subsequence converging a.e.  (This is the `ℝ≥0∞` analogue of
  `TendstoInMeasure.exists_seq_tendsto_ae`, proved directly rather than through convergence in
  measure, so that no `SigmaFinite` instance is needed.)

`ae_eq_of_lintegral_iSup_sq_tendsto_zero` gives sequence independence, stated with **pointwise** convergence
hypotheses rather than `TendstoUniformlyOn`: that is the weakest form the conclusion needs, and the
uniform convergence produced by `exists_tendsto_of_summable_supIncr` supplies it immediately.
-/

set_option autoImplicit false

open Filter MeasureTheory Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

/-! ## a.e. convergence from summable integrals -/

/-- Summable integrals force the integrands to `0` a.e.  No finiteness of `μ` is used. -/
theorem ae_tendsto_zero_of_tsum_lintegral_ne_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : ℕ → Ω → ℝ≥0∞} (hD : ∀ k, AEMeasurable (D k) μ)
    (h : (∑' k : ℕ, ∫⁻ ω, D k ω ∂μ) ≠ ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => D k ω) atTop (𝓝 0) := by
  have hfin : (∫⁻ ω, ∑' k : ℕ, D k ω ∂μ) ≠ ⊤ := by rw [lintegral_tsum hD]; exact h
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hD) hfin] with ω hω
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne

/-- The `ℝ≥0∞` `L¹`-to-a.e. extraction, with no `SigmaFinite` hypothesis. -/
theorem exists_subseq_ae_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : ℕ → Ω → ℝ≥0∞} (hD : ∀ k, AEMeasurable (D k) μ)
    (h : Tendsto (fun k => ∫⁻ ω, D k ω ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂μ, Tendsto (fun k => D (φ k) ω) atTop (𝓝 0) := by
  have hev : ∀ n : ℕ, ∀ᶠ k in atTop, (∫⁻ ω, D k ω ∂μ) < ((4 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    refine (tendsto_order.1 h).2 _ (pos_iff_ne_zero.mpr (pow_ne_zero n ?_))
    exact ENNReal.inv_ne_zero.mpr (by norm_num)
  obtain ⟨φ, hφ, hφle⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ae_tendsto_zero_of_tsum_lintegral_ne_top (fun k => hD (φ k)) ?_⟩
  refine ne_top_of_le_ne_top tsum_geometric_four_inv_ne_top ?_
  exact ENNReal.tsum_le_tsum fun k => (hφle k).le

/-! ## Step 6: independence of the approximating sequence -/

/-- **Step 6.**  Two families of pathwise approximations whose difference tends to `0` in the
maximal `L²` sense over `[0, T]` have the same a.e. pointwise limit on `[0, T]`. -/
theorem ae_eq_of_lintegral_iSup_sq_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B : ℕ → Ω → ℝ≥0 → ℝ} {Z W : Ω → ℝ≥0 → ℝ} (T : ℝ≥0)
    (hA : ∀ᵐ ω ∂μ, ∀ t ≤ T, Tendsto (fun k => A k ω t) atTop (𝓝 (Z ω t)))
    (hB : ∀ᵐ ω ∂μ, ∀ t ≤ T, Tendsto (fun k => B k ω t) atTop (𝓝 (W ω t)))
    (hmeas : ∀ k, AEMeasurable (fun ω => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
      ENNReal.ofReal ((A k ω t - B k ω t) ^ 2)) μ)
    (h : Tendsto (fun k => ∫⁻ ω, ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
      ENNReal.ofReal ((A k ω t - B k ω t) ^ 2) ∂μ) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, Z ω t = W ω t := by
  obtain ⟨φ, hφ, hae⟩ := exists_subseq_ae_tendsto_zero hmeas h
  filter_upwards [hA, hB, hae] with ω hAω hBω hD
  intro t ht
  -- the squared difference along the subsequence tends to `0`
  have hsq : Tendsto (fun k => ENNReal.ofReal ((A (φ k) ω t - B (φ k) ω t) ^ 2)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD
      (fun _ => bot_le) fun k => ?_
    exact le_iSup₂ (f := fun s (_ : s ≤ T) =>
      ENNReal.ofReal ((A (φ k) ω s - B (φ k) ω s) ^ 2)) t ht
  have hsqReal : Tendsto (fun k => (A (φ k) ω t - B (φ k) ω t) ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (by simp)).comp hsq
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_zero]
      using this
  have hdiff : Tendsto (fun k => A (φ k) ω t - B (φ k) ω t) atTop (𝓝 0) := by
    have habs : Tendsto (fun k => |A (φ k) ω t - B (φ k) ω t|) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hsqReal
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using this
    exact tendsto_zero_iff_abs_tendsto_zero _ |>.mpr habs
  -- both subsequences converge, and their difference vanishes
  have hAsub : Tendsto (fun k => A (φ k) ω t) atTop (𝓝 (Z ω t)) :=
    (hAω t ht).comp hφ.tendsto_atTop
  have hBsub : Tendsto (fun k => B (φ k) ω t) atTop (𝓝 (W ω t)) :=
    (hBω t ht).comp hφ.tendsto_atTop
  have hZW : Tendsto (fun k => B (φ k) ω t) atTop (𝓝 (Z ω t - 0)) := by
    have : Tendsto (fun k => A (φ k) ω t - (A (φ k) ω t - B (φ k) ω t)) atTop
        (𝓝 (Z ω t - 0)) := hAsub.sub hdiff
    simpa only [sub_sub_cancel] using this
  rw [sub_zero] at hZW
  exact tendsto_nhds_unique hZW hBsub

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
