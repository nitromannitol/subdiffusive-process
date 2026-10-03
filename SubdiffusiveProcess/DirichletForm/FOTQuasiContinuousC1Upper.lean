module

public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuous
public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousConvex
public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousC1Measure

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}

/-- Closedness gives the upper chain inequality at the quasi-continuous representative. -/
theorem EnergyFamily.quasiContinuous_chain_le {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    {L : ℝ≥0} (hL : LipschitzWith L Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (q.rep u hu x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal ≤ ∫ x in B, (deriv Φ (q.rep u hu x)) ^ 2 ∂Γ.measure u := by
  classical
  haveI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  obtain ⟨un, fn, hun, hfn, henergy, hLp, hbound⟩ := exists_core_energy_approx F h hu
  obtain ⟨s, hs, hsae⟩ := q.approx_ae u hu un hun fn hfn henergy
  let v : ℕ → Lp ℝ 2 m := fun n => hL.compLp hΦ0 (un (s n))
  have hv : ∀ n, v n ∈ F.domain := fun n =>
    lipschitz_comp_mem F hL hΦ0 (hun (s n)).1 (hL.coeFn_compLp hΦ0 (un (s n))) |>.1
  have hvE : ∀ n, F.form (v n) (v n) ≤ (L : ℝ) ^ 2 * (2 * F.form u u + 2) := by
    intro n
    exact (lipschitz_comp_mem F hL hΦ0 (hun (s n)).1
      (hL.coeFn_compLp hΦ0 (un (s n)))).2.trans
        (mul_le_mul_of_nonneg_left (hbound (s n)) (sq_nonneg _))
  have heq : hL.compLp hΦ0 u = w := Lp.ext
    (((hL.coeFn_compLp hΦ0 u).trans ((q.ae_rep u hu).fun_comp Φ)).trans hwae.symm)
  have hvlim : Tendsto v atTop (𝓝 w) := by
    simpa only [heq] using! (hL.continuous_compLp hΦ0).tendsto u |>.comp (hLp.comp hs.tendsto_atTop)
  let a : ℕ → X → ℝ := fun n x => (deriv Φ (fn (s n) x)) ^ 2
  let a0 : X → ℝ := fun x => (deriv Φ (q.rep u hu x)) ^ 2
  have hderiv : ∀ r : ℝ, |deriv Φ r| ≤ L := fun r => by
    simpa only [Real.norm_eq_abs] using! norm_deriv_le_of_lipschitz hL (x₀ := r)
  have haK : ∀ n x, |a n x| ≤ (L : ℝ) ^ 2 := by
    intro n x
    change |deriv Φ (fn (s n) x) ^ 2| ≤ (L : ℝ) ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    calc
      _ = |deriv Φ (fn (s n) x)| ^ 2 := (sq_abs _).symm
      _ ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hderiv _) 2
  have ha0K : ∀ x, |a0 x| ≤ (L : ℝ) ^ 2 := by
    intro x
    change |deriv Φ (q.rep u hu x) ^ 2| ≤ (L : ℝ) ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    calc
      _ = |deriv Φ (q.rep u hu x)| ^ 2 := (sq_abs _).symm
      _ ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hderiv _) 2
  have ha : ∀ n, Measurable (a n) := fun n =>
    (hΦ.continuous_deriv le_rfl |>.comp (hfn (s n)).1 |>.pow 2).measurable
  have hfixed : Tendsto (fun n => ∫ x in B, a n x ∂Γ.measure u) atTop
      (𝓝 (∫ x in B, a0 x ∂Γ.measure u)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (L : ℝ) ^ 2)
    · intro n
      exact (ha n).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! haK n x
    · filter_upwards [ae_restrict_of_ae (hsae u hu)] with x hx
      exact ((hΦ.continuous_deriv le_rfl).tendsto (q.rep u hu x) |>.comp hx).pow 2
  let D : ℕ → ℝ := fun n => Real.sqrt (F.form (un (s n) - u) (un (s n) - u)) *
    (Real.sqrt (F.form (un (s n)) (un (s n))) + Real.sqrt (F.form u u))
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have hg := henergy.comp hs.tendsto_atTop
    have hsub : Tendsto (fun n => F.form (un (s n) - u) (un (s n) - u)) atTop (𝓝 0) :=
      squeeze_zero (fun n => F.form_nonneg _ (F.domain.sub_mem (hun (s n)).1 hu))
        (fun n => F.form_le_energyNormSq) hg
    have hself := F.tendsto_form_self_of_tendsto_energyNormSq
      (fun n => (hun (s n)).1) hu hg
    have h1 := Real.continuous_sqrt.tendsto 0 |>.comp hsub
    have h2 := Real.continuous_sqrt.tendsto (F.form u u) |>.comp hself
    simpa only [Real.sqrt_zero, zero_mul] using! h1.mul (h2.add_const (Real.sqrt (F.form u u)))
  have hdiff : Tendsto (fun n => (∫ x in B, a n x ∂Γ.measure (un (s n))) -
      ∫ x in B, a n x ∂Γ.measure u) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => 2 * (L : ℝ) ^ 2 * D n)
    · intro n
      haveI : IsFiniteMeasure (Γ.measure (un (s n))) := ⟨Γ.finite _ (hun (s n)).1⟩
      rw [Real.norm_eq_abs]
      exact bounded_setIntegral_difference_bound _ _ (by positivity)
        (sq_nonneg _) (fun A hA => Γ.difference_bound (hun (s n)).1 hu hA)
        (ha n) (haK n) hB
    · simpa only [mul_zero] using! hD0.const_mul (2 * (L : ℝ) ^ 2)
  have hvar : Tendsto (fun n => ∫ x in B, a n x ∂Γ.measure (un (s n))) atTop
      (𝓝 (∫ x in B, a0 x ∂Γ.measure u)) := by
    simpa only [sub_add_cancel, zero_add] using! hdiff.add hfixed
  have hidentity : ∀ n, (Γ.measure (v n) B).toReal = ∫ x in B, a n x ∂Γ.measure (un (s n)) := by
    intro n
    apply Γ.core_chain h (hun (s n)) (hfn (s n)).1 (hfn (s n)).2.2.2 Φ hΦ hΦ0 (hv n)
    · exact (hL.coeFn_compLp hΦ0 (un (s n))).trans ((hfn (s n)).2.2.2.fun_comp Φ)
    · exact hB
  have hmass : Tendsto (fun n => (Γ.measure (v n) B).toReal) atTop
      (𝓝 (∫ x in B, a0 x ∂Γ.measure u)) := by simpa only [hidentity] using! hvar
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmass.eventually
    (Iio_mem_nhds (lt_add_of_pos_right _ hε)))
  have hmax : Tendsto (fun n : ℕ => max n N) atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left n N) tendsto_id
  exact (Γ.local_limsup (fun n => hv (max n N)) (hvlim.comp hmax)
    (fun n => hvE (max n N)) hB (fun n => (hN (max n N) (le_max_right _ _)).le)).2

end DirichletForm.FOTConstruction
