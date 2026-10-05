module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamily
public import SubdiffusiveProcess.DirichletForm.FOTDomainHilbert

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- Small energy cutoffs have small integrals against the energy measure of a fixed core element. -/
theorem EnergyFamily.cutoff_integral_small {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    {uc : X → ℝ} (huc : Continuous uc) (huae : ⇑u =ᵐ[m] uc)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (v : Lp ℝ 2 m), F.toClosedForm.MemCoreOn U v →
      ∀ f : X → ℝ, Continuous f → ⇑v =ᵐ[m] f → (∀ x, f x ∈ Icc 0 1) →
        Real.sqrt (F.energyNormSq v) < δ → ∫ x, f x ∂Γ.measure u < ε := by
  classical
  by_contra hsmall
  push Not at hsmall
  have hs : ∀ n : ℕ, ∃ (v : Lp ℝ 2 m), F.toClosedForm.MemCoreOn U v ∧
      ∃ f : X → ℝ, Continuous f ∧ ⇑v =ᵐ[m] f ∧ (∀ x, f x ∈ Icc 0 1) ∧
      Real.sqrt (F.energyNormSq v) < 1 / ((n : ℝ) + 1) ∧ ε ≤ ∫ x, f x ∂Γ.measure u := by
    intro n
    exact hsmall (1 / ((n : ℝ) + 1)) (by positivity)
  choose v hv f hf hfae hf01 hcost hbad using hs
  have hnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (Real.le_sqrt_of_sq_le (F.sq_norm_le_energyNormSq (hv n).1)).trans (hcost n).le
  have hvE : ∀ n, F.form (v n) (v n) ≤ 1 := by
    intro n
    have he := F.energyNormSq_nonneg (hv n).1
    have hsq := Real.sq_sqrt he
    have hb : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hc := (hcost n).le.trans hb
    have hh := F.form_le_energyNormSq (u := v n)
    nlinarith [Real.sqrt_nonneg (F.energyNormSq (v n))]
  obtain ⟨M, hM⟩ := ae_abs_le_of_memCoreOn hu
  let R : ℝ := max M 1
  have hR : 0 ≤ R := zero_le_one.trans (le_max_right _ _)
  have huR : ∀ᵐ x ∂m, |u x| ≤ R := hM.mono fun _ hx => hx.trans (le_max_left _ _)
  have hvR : ∀ n, ∀ᵐ x ∂m, |v n x| ≤ R := by
    intro n
    filter_upwards [hfae n] with x hx
    rw [hx, abs_of_nonneg (hf01 n x).1]
    exact (hf01 n x).2.trans (le_max_right _ _)
  choose w hw hwae hwE using fun n => exists_mul_mem_form_le F hu.1 (hv n).1 huR (hvR n)
  have hwbound : ∀ n, F.form (w n) (w n) ≤ 8 * R ^ 2 * (F.form u u + 1) := by
    intro n
    exact (hwE n).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hvE n)) (by positivity))
  have hwnorm : Tendsto (fun n => ‖w n‖) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun n => R * ‖v n‖) (fun n => norm_nonneg _) (fun n => ?_) ?_
    · apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hwae n, huR] with x hx hxu
      simp only [hx, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right hxu (abs_nonneg _)
    · simpa only [mul_zero] using hnorm.const_mul R
  have hform := _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.EnergyHilbert.weak_null_form_tendsto_zero F.toClosedForm w hw _ hwbound hwnorm u hu.1
  obtain ⟨u2, hu2, hu2ae⟩ := exists_mul_mem F hu.1 hu.1 huR huR
  have hform2 := _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.EnergyHilbert.weak_null_form_tendsto_zero F.toClosedForm v
    (fun n => (hv n).1) 1 hvE hnorm u2 hu2
  have hlim : Tendsto (fun n => ∫ x, f n x ∂Γ.measure u) atTop (𝓝 0) := by
    have hidentity : ∀ n, (∫ x, f n x ∂Γ.measure u) = F.form u (w n) - (1 / 2 : ℝ) * F.form u2 (v n) := by
      intro n
      apply Γ.defining u (v n) hu (hv n) uc (f n) huc (hf n) huae (hfae n) (w n) u2 (hw n) hu2
      · filter_upwards [hwae n, huae, hfae n] with x hx hxu hxv
        rw [hx, hxu, hxv]
      · filter_upwards [hu2ae, huae] with x hx hxu
        rw [hx, hxu, pow_two]
    simpa only [hidentity, mul_zero, sub_zero] using hform.sub (hform2.const_mul (1 / 2 : ℝ))
  have hle : ε ≤ (0 : ℝ) := ge_of_tendsto hlim (Eventually.of_forall hbad)
  exact (not_le.mpr hε) hle

end SubdiffusiveProcess.DirichletForm.FOTConstruction
