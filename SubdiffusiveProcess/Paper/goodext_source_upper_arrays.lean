import SubdiffusiveProcess.Paper.goodext_source_absorption_arrays
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Retain prescribed limits when extracting a common almost sure subsequence. -/
theorem aux_goodext_source_upper_arrays_extract
    {Ω Cells : Type} [MeasurableSpace Ω] [Countable Cells]
    (P : Measure Ω) (X : Cells → ℕ → Ω → ℝ) (lim : Cells → Ω → ℝ)
    (hX : ∀ b, TendstoInMeasure P (X b) atTop (lim b)) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ᵐ omega ∂P, ∀ b,
      Tendsto (fun n => X b (psi n) omega) atTop (𝓝 (lim b omega)) := by
  letI := Encodable.ofCountable Cells
  let diff : ℕ → ℕ → Ω → ℝ := fun j n omega =>
    match Encodable.decode (α := Cells) j with
    | none => 0
    | some b => X b n omega - lim b omega
  have hd : ∀ j eps, 0 < eps →
      Tendsto (fun n => P {omega | eps ≤ |diff j n omega|}) atTop (𝓝 0) := by
    intro j eps heps
    cases hj : Encodable.decode (α := Cells) j with
    | none => simpa only [diff, hj, abs_zero, not_le.mpr heps, Set.setOf_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    | some b => simpa only [diff, hj, Real.dist_eq] using
        (tendstoInMeasure_iff_dist.mp (hX b) eps heps)
  obtain ⟨psi, hpsi, hae⟩ := exists_strictMono_ae_forall_tendsto_zero P diff hd id tendsto_id
  refine ⟨psi, hpsi, ?_⟩
  filter_upwards [hae] with omega h
  intro b
  have he := h (Encodable.encode b)
  simp only [diff, Encodable.encodek, id_eq] at he
  simpa only [sub_add_cancel, zero_add] using he.add_const (lim b omega)

/-- The original upper-normalization arrays yield actual finite-coefficient caps
on one common refinement. Reference and coefficient limits are retained for every
cell, so subsequent harmonic extraction can preserve all these bounds. -/
theorem goodext_source_upper_arrays
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hMH : InfraredCharacterization M H)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (hCutoff : StrictMono cutoff) (env : ℕ → Ω → BilateralField d)
    (beta : ℝ) (Cells : Type) [Countable Cells] (level : Cells → ℕ)
    (centre : Cells → SpatialCoordinates d)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (hEnv : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure)
    (hEnvConv : ∀ᵐ omega ∂P, Tendsto (fun n => env n omega) atTop (𝓝 (field omega)))
    (eRef : ℕ → ℝ) (heRef : ∀ k, 0 < eRef k)
    (hRefLim : ∀ k : ℕ,
      let kappa : ℕ → ℝ := fun N => Real.exp (((N : ℝ) + 1) *
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
      Tendsto (fun n => kappa (cutoff n - k) / kappa (cutoff n)) atTop (𝓝 (eRef k)))
    (hi : Cells → BilateralField d → ℝ) (hMeas : ∀ b, Measurable (hi b))
    (hHi : ∀ b, TendstoInMeasure (chaosSampleLaw M).toMeasure (fun n omega =>
      E.Lam (centre b) ((3 : ℝ) ^ (-(level b : ℤ))) (zpow_pos (by norm_num) _)
        (cutoffPositiveCoefficient M H omega (cutoff n) (centre b) (zpow_pos (by norm_num) _))
        (centre b) ((3 : ℝ) ^ (-(level b : ℤ))) ((beta - 1 / 2) / 4) 2 /
        gcat_sN M H (cutoff n) (level b : ℤ) (centre b) omega) atTop (hi b))
 :
    let side := fun b => (3 : ℝ) ^ (-(level b : ℤ))
    let ref := fun b omega => eRef (level b) * Real.exp
      (H (field omega) (centre b) + ∑ j ∈ Finset.range (level b), (field omega) (-(j : ℤ)) (centre b))
    let upper := fun b n omega => E.Lam (centre b) (side b) (zpow_pos (by norm_num) _)
      (cutoffPositiveCoefficient M H (env n omega) (cutoff n)
        (centre b) (zpow_pos (by norm_num) _))
      (centre b) (side b) ((beta - 1 / 2) / 4) 2
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ᵐ omega ∂P, ∀ b,
      0 < ref b omega ∧
      Tendsto (fun n => gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b)
        (env (psi n) omega)) atTop (𝓝 (ref b omega)) ∧
      Tendsto (fun n => upper b (psi n) omega) atTop (𝓝 (hi b (field omega) * ref b omega)) ∧
      ∀ cap : ℝ, 0 < cap → hi b (field omega) ≤ cap →
        ∀ᶠ n in atTop, upper b (psi n) omega ≤ (2 * cap) * ref b omega := by
  intro side ref upper
  obtain ⟨psi, hpsi, hScale, hNorm⟩ := aux_goodext_source_absorption_arrays_limits d E M H hMH
    Ω P cutoff hCutoff env beta Cells level centre field hfield hEnv hEnvConv
    eRef heRef hRefLim hi hMeas hHi
  let scale : Cells → ℕ → Ω → ℝ := fun b n omega =>
    gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b) (env (psi n) omega)
  obtain ⟨rho, hrho, hAE⟩ := aux_goodext_source_upper_arrays_extract P
    (fun b n omega => upper b (psi n) omega / scale b n omega)
    (fun b omega => hi b (field omega)) hNorm
  refine ⟨fun n => psi (rho n), hpsi.comp hrho, ?_⟩
  filter_upwards [ae_all_iff.mpr hScale, hAE] with omega hscale hnorm
  intro b
  have href : 0 < ref b omega := (hscale b).1
  have hsc : Tendsto (fun n => scale b (rho n) omega) atTop (𝓝 (ref b omega)) :=
    (hscale b).2.comp hrho.tendsto_atTop
  have hpos : ∀ᶠ n in atTop, 0 < scale b (rho n) omega :=
    hsc.eventually (eventually_gt_nhds href)
  have hproduct := (hnorm b).mul hsc
  have hupper : Tendsto (fun n => upper b (psi (rho n)) omega) atTop
      (𝓝 (hi b (field omega) * ref b omega)) := by
    apply hproduct.congr'
    filter_upwards [hpos] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  refine ⟨href, hsc, hupper, ?_⟩
  intro cap hcap hb
  have hlt : hi b (field omega) * ref b omega < (2 * cap) * ref b omega :=
    mul_lt_mul_of_pos_right (by linarith only [hcap, hb]) href
  exact (hupper.eventually (eventually_lt_nhds hlt)).mono (fun _ h => h.le)
end Paper
