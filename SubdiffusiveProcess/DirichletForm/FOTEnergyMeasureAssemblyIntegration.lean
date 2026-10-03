module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblySigned
public import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyProducts
public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuous

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- Strong energy convergence and bounded convergence of test functions
pass to their energy-measure integrals. -/
theorem EnergyFamily.integral_tendsto_of_energy
    {F : _root_.DirichletForm m} {U : Set X} (Γ : EnergyFamily F U)
    {un : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hun : ∀ n, un n ∈ F.domain) (hu : u ∈ F.domain)
    (henergy : Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0))
    (fn : ℕ → X → ℝ) (f : X → ℝ) (hfn : ∀ n, Measurable (fn n))
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ n x, ‖fn n x‖ ≤ R)
    (hf : ∀ᵐ x ∂Γ.measure u, Tendsto (fun n => fn n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, fn n x ∂Γ.measure (un n)) atTop
      (𝓝 (∫ x, f x ∂Γ.measure u)) := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  have hfixed := tendsto_integral_of_dominated_convergence (fun _ : X => R)
    (fun n => (hfn n).aestronglyMeasurable) (integrable_const R)
    (fun n => Eventually.of_forall (hR n)) hf
  have hformdiff : Tendsto (fun n => F.form (un n - u) (un n - u)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => F.form_nonneg _ (F.domain.sub_mem (hun n) hu))
      (fun n => F.toClosedForm.form_le_energyNormSq) henergy
  have hformself := F.toClosedForm.tendsto_form_self_of_tendsto_energyNormSq hun hu henergy
  have hboundlim : Tendsto (fun n => 2 * R *
      (Real.sqrt (F.form (un n - u) (un n - u)) *
        (Real.sqrt (F.form (un n) (un n)) + Real.sqrt (F.form u u)))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, zero_mul, mul_zero] using!
      (((Real.continuous_sqrt.tendsto 0).comp hformdiff).mul
        (((Real.continuous_sqrt.tendsto (F.form u u)).comp hformself).add_const
          (Real.sqrt (F.form u u)))).const_mul (2 * R)
  have herror : Tendsto (fun n => (∫ x, fn n x ∂Γ.measure (un n)) -
      ∫ x, fn n x ∂Γ.measure u) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hboundlim
    letI : IsFiniteMeasure (Γ.measure (un n)) := ⟨Γ.finite (un n) (hun n)⟩
    exact assembly_integral_sub_bound _ _ (fn n) (hfn n) R hR0 (hR n) _
      (fun B hB => Γ.difference_bound (hun n) hu hB)
  have hsum := herror.add hfixed
  simpa only [zero_add, sub_add_cancel] using! hsum

/-- Bounded continuous domain representatives satisfy the defining identity. -/
theorem EnergyFamily.defining_bounded [T2Space X] [LocallyCompactSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U)
    (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u φ : Lp ℝ 2 m} (hu : u ∈ F.domain) (hφ : φ ∈ F.domain)
    {uc φc : X → ℝ} (huc : Continuous uc) (hφc : Continuous φc)
    (huae : ⇑u =ᵐ[m] uc) (hφae : ⇑φ =ᵐ[m] φc)
    (R : ℝ≥0) (huR : ∀ x, |uc x| ≤ R) (hφR : ∀ x, |φc x| ≤ R)
    {uφ u2 : Lp ℝ 2 m} (huφ : uφ ∈ F.domain) (hu2 : u2 ∈ F.domain)
    (hprod : ⇑uφ =ᵐ[m] fun x => uc x * φc x) (hsq : ⇑u2 =ᵐ[m] fun x => uc x ^ 2) :
    (∫ x, φc x ∂Γ.measure u) = F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
  have huRae : ∀ᵐ x ∂m, |u x| ≤ R := huae.mono fun x hx => hx ▸ huR x
  have hφRae : ∀ᵐ x ∂m, |φ x| ≤ R := hφae.mono fun x hx => hx ▸ hφR x
  obtain ⟨un₀, fn₀, hun₀, hfn₀, henu₀⟩ := exists_bounded_energy_approx F h hu huRae
  obtain ⟨φn₀, gn₀, hφn₀, hgn₀, henφ₀⟩ := exists_bounded_energy_approx F h hφ hφRae
  obtain ⟨seq, hseq, hgnlim⟩ := q.approx_ae φ hφ φn₀ hφn₀ gn₀
    (fun n => ⟨(hgn₀ n).1, (hgn₀ n).2.1, (hgn₀ n).2.2.1, (hgn₀ n).2.2.2.1⟩) henφ₀
  let un := un₀ ∘ seq
  let φn := φn₀ ∘ seq
  let fn := fn₀ ∘ seq
  let gn := gn₀ ∘ seq
  have hun : ∀ n, F.toClosedForm.MemCoreOn U (un n) := fun n => hun₀ (seq n)
  have hφn : ∀ n, F.toClosedForm.MemCoreOn U (φn n) := fun n => hφn₀ (seq n)
  have henu : Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0) :=
    henu₀.comp hseq.tendsto_atTop
  have henφ : Tendsto (fun n => F.energyNormSq (φn n - φ)) atTop (𝓝 0) :=
    henφ₀.comp hseq.tendsto_atTop
  have hunlim : Tendsto un atTop (𝓝 u) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs : Tendsto (fun n => ‖un n - u‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _)
        (fun n => F.toClosedForm.sq_norm_le_energyNormSq (F.domain.sub_mem (hun n).1 hu)) henu
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using!
      (Real.continuous_sqrt.tendsto 0).comp hs
  have hφnlim : Tendsto φn atTop (𝓝 φ) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs : Tendsto (fun n => ‖φn n - φ‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _)
        (fun n => F.toClosedForm.sq_norm_le_energyNormSq (F.domain.sub_mem (hφn n).1 hφ)) henφ
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using!
      (Real.continuous_sqrt.tendsto 0).comp hs
  have hunR : ∀ n, ∀ᵐ x ∂m, |un n x| ≤ R := fun n =>
    (hfn₀ (seq n)).2.2.2.1.mono fun x hx => hx ▸ (hfn₀ (seq n)).2.2.2.2 x
  have hφnR : ∀ n, ∀ᵐ x ∂m, |φn n x| ≤ R := fun n =>
    (hgn₀ (seq n)).2.2.2.1.mono fun x hx => hx ▸ (hgn₀ (seq n)).2.2.2.2 x
  choose pn hpn hpnrep hpnE using fun n =>
    exists_mul_mem_form_le F (hun n).1 (hφn n).1 (hunR n) (hφnR n)
  choose qn hqn hqnrep hqnE using fun n =>
    exists_mul_mem_form_le F (hun n).1 (hun n).1 (hunR n) (hunR n)
  obtain ⟨Cu, hCu⟩ := assembly_energy_bound F (fun n => (hun n).1) hu henu
  obtain ⟨Cφ, hCφ⟩ := assembly_energy_bound F (fun n => (hφn n).1) hφ henφ
  have hpnlim : Tendsto pn atTop (𝓝 uφ) :=
    assembly_product_tendsto F (fun n => (hun n).1) (fun n => (hφn n).1) hu hφ R
      hunR hφnR huRae hφRae (by
        filter_upwards [hprod, huae, hφae] with x hx hy hz
        rw [hx, hy, hz]) pn hpnrep hunlim hφnlim
  have hqnlim : Tendsto qn atTop (𝓝 u2) :=
    assembly_product_tendsto F (fun n => (hun n).1) (fun n => (hun n).1) hu hu R
      hunR hunR huRae huRae (by
        filter_upwards [hsq, huae] with x hx hy
        rw [hx, hy, pow_two]) qn hqnrep hunlim hunlim
  have hterm1 := assembly_form_tendsto F (fun n => (hun n).1) hpn hu huφ henu
    (8 * (R : ℝ) ^ 2 * (Cu + Cφ))
    (fun n => (hpnE n).trans (by gcongr; exact hCu n; exact hCφ n)) hpnlim
  have hterm2 := assembly_form_tendsto F (fun n => (hφn n).1) hqn hφ hu2 henφ
    (8 * (R : ℝ) ^ 2 * (Cu + Cu))
    (fun n => (hqnE n).trans (by gcongr; exact hCu n; exact hCu n)) hqnlim
  have hintlim : Tendsto (fun n => ∫ x, gn n x ∂Γ.measure (un n)) atTop
      (𝓝 (∫ x, φc x ∂Γ.measure u)) := by
    apply Γ.integral_tendsto_of_energy (fun n => (hun n).1) hu henu gn φc
      (fun n => (hgn₀ (seq n)).1.measurable) R R.coe_nonneg
      (fun n x => (hgn₀ (seq n)).2.2.2.2 x)
    filter_upwards [hgnlim u hu, q.continuous_agree φ hφ φc hφc hφae u hu] with x hx hy
    rw [← hy]
    exact hx
  have hid : ∀ n, (∫ x, gn n x ∂Γ.measure (un n)) =
      F.form (un n) (pn n) - (1 / 2 : ℝ) * F.form (φn n) (qn n) := by
    intro n
    rw [F.form_symm (φn n) (hφn n).1 (qn n) (hqn n)]
    apply Γ.defining (un n) (φn n) (hun n) (hφn n) (fn n) (gn n)
      (hfn₀ (seq n)).1 (hgn₀ (seq n)).1
      (hfn₀ (seq n)).2.2.2.1 (hgn₀ (seq n)).2.2.2.1 (pn n) (qn n) (hpn n) (hqn n)
    · filter_upwards [hpnrep n, (hfn₀ (seq n)).2.2.2.1,
        (hgn₀ (seq n)).2.2.2.1] with x hx hy hz
      simpa only [un, φn, fn, gn, Function.comp_def, hy, hz] using! hx
    · filter_upwards [hqnrep n, (hfn₀ (seq n)).2.2.2.1] with x hx hy
      simpa only [un, fn, Function.comp_def, hy, pow_two] using! hx
  have hrhs := hterm1.sub (hterm2.const_mul (1 / 2 : ℝ))
  rw [F.form_symm φ hφ u2 hu2] at hrhs
  exact tendsto_nhds_unique hintlim (hrhs.congr fun n => (hid n).symm)

end DirichletForm.FOTConstruction
