module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamily

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

theorem EnergyFamily.measure_tendsto_of_energy
    {F : _root_.DirichletForm m} {U : Set X} (Γ : EnergyFamily F U)
    {un : ℕ → Lp ℝ 2 m} (hun : ∀ n, un n ∈ F.domain)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (hlim : Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0))
    {B : Set X} (hB : MeasurableSet B) :
    Tendsto (fun n => (Γ.measure (un n) B).toReal) atTop (𝓝 (Γ.measure u B).toReal) := by
  have he : Tendsto (fun n => F.form (un n - u) (un n - u)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => F.form_nonneg _ (F.domain.sub_mem (hun n) hu))
      (fun n => ?_) hlim
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hself := F.toClosedForm.tendsto_form_self_of_tendsto_energyNormSq hun hu hlim
  have hbound : Tendsto
      (fun n => Real.sqrt (F.form (un n - u) (un n - u)) *
        (Real.sqrt (F.form (un n) (un n)) + Real.sqrt (F.form u u))) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp he
    have hm := hs.mul (((Real.continuous_sqrt.tendsto (F.form u u)).comp hself).add_const
      (Real.sqrt (F.form u u)))
    simpa only [Function.comp_def, Real.sqrt_zero, zero_mul] using! hm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbound
  simpa only [Real.norm_eq_abs] using! Γ.difference_bound (hun n) hu hB

end DirichletForm.FOTConstruction
