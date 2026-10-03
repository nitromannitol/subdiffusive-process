module

public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousC1Upper
public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousC1Signed

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

/-- The core chain and cross-chain rules control differences of composed core elements. -/
theorem EnergyFamily.c1_comp_form_sub_le {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {p r u : Lp ℝ 2 m}
    (hp : F.toClosedForm.MemCoreOn U p) (hr : F.toClosedForm.MemCoreOn U r)
    (hu : u ∈ F.domain) {pc rc : X → ℝ} (hpc : Continuous pc) (hrc : Continuous rc)
    (hpae : ⇑p =ᵐ[m] pc) (hrae : ⇑r =ᵐ[m] rc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {L : ℝ≥0} (hL : LipschitzWith L Φ) (hΦ0 : Φ 0 = 0)
    {a b : Lp ℝ 2 m} (ha : a ∈ F.domain) (hb : b ∈ F.domain)
    (haa : ⇑a =ᵐ[m] fun x => Φ (pc x)) (hba : ⇑b =ᵐ[m] fun x => Φ (rc x))
    {C : ℝ} (hrC : Real.sqrt (F.form r r) ≤ C) (huC : Real.sqrt (F.form u u) ≤ C) :
    F.form (a - b) (a - b) ≤
      (∫ x, (deriv Φ (pc x) - deriv Φ (rc x)) ^ 2 ∂Γ.measure u) +
      2 * (L : ℝ) ^ 2 * (Real.sqrt (F.form (p - u) (p - u)) *
        (Real.sqrt (F.form p p) + Real.sqrt (F.form u u)) +
        Real.sqrt (F.form (r - u) (r - u)) *
        (Real.sqrt (F.form r r) + Real.sqrt (F.form u u))) +
      4 * (L : ℝ) ^ 2 * C *
        (Real.sqrt (F.form (p - u) (p - u)) + Real.sqrt (F.form (r - u) (r - u))) := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  letI : IsFiniteMeasure (Γ.measure p) := ⟨Γ.finite p hp.1⟩
  letI : IsFiniteMeasure (Γ.measure r) := ⟨Γ.finite r hr.1⟩
  let dp : X → ℝ := fun x => deriv Φ (pc x)
  let dr : X → ℝ := fun x => deriv Φ (rc x)
  have hdp : Measurable dp := (hΦ.continuous_deriv le_rfl |>.comp hpc).measurable
  have hdr : Measurable dr := (hΦ.continuous_deriv le_rfl |>.comp hrc).measurable
  have hdpL : ∀ x, |dp x| ≤ L := fun x => norm_deriv_le_of_lipschitz hL
  have hdrL : ∀ x, |dr x| ≤ L := fun x => norm_deriv_le_of_lipschitz hL
  have hdp2 : ∀ x, |dp x ^ 2| ≤ (L : ℝ) ^ 2 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hdpL x) 2
  have hdr2 : ∀ x, |dr x ^ 2| ≤ (L : ℝ) ^ 2 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hdrL x) 2
  have hprod : ∀ x, |dp x * dr x| ≤ (L : ℝ) ^ 2 := fun x => by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hdpL x) (hdrL x) (abs_nonneg _) L.coe_nonneg
  have hi : ∀ (f : X → ℝ), Measurable f → (∀ x, |f x| ≤ (L : ℝ) ^ 2) → Integrable f (Γ.measure u) := by
    intro f hf hfL
    exact (integrable_const ((L : ℝ) ^ 2)).mono' hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfL x)
  have hip := hi (fun x => dp x ^ 2) (hdp.pow_const 2) hdp2
  have hir := hi (fun x => dr x ^ 2) (hdr.pow_const 2) hdr2
  have hipr := hi (fun x => dp x * dr x) (hdp.mul hdr) hprod
  have hmeasurep := bounded_integral_difference_bound (Γ.measure p) (Γ.measure u)
    (by positivity) (sq_nonneg (L : ℝ)) (fun B hB => Γ.difference_bound hp.1 hu hB)
    (hdp.pow_const 2) hdp2
  have hmeasurer := bounded_integral_difference_bound (Γ.measure r) (Γ.measure u)
    (by positivity) (sq_nonneg (L : ℝ)) (fun B hB => Γ.difference_bound hr.1 hu hB)
    (hdr.pow_const 2) hdr2
  have hcross := c1_signedIntegral_sub_bound (Γ.cross p r) (Γ.cross u u) univ .univ
    (fun x => dp x * dr x) (hdp.mul hdr) ((L : ℝ) ^ 2) (sq_nonneg _)
    (fun x => by simpa only [Real.norm_eq_abs, Pi.mul_apply] using! hprod x) _
    (fun B hB => Γ.cross_difference_bound hp.1 hr.1 hu hrC huC hB)
  have hself := Γ.cross_self_integral hu univ .univ _ (hdp.mul hdr) _
    (fun x => by simpa only [Real.norm_eq_abs, Pi.mul_apply] using! hprod x)
  change signedIntegralOn (Γ.cross u u) univ (fun x => dp x * dr x) = _ at hself
  rw [hself, Measure.restrict_univ] at hcross
  simp only [Pi.mul_apply] at hcross
  have haid := Γ.core_chain h hp hpc hpae Φ hΦ hΦ0 ha haa (B := univ) .univ
  have hbid := Γ.core_chain h hr hrc hrae Φ hΦ hΦ0 hb hba (B := univ) .univ
  have hcrossid := Γ.core_cross_chain h hp hr hpc hrc hpae hrae Φ Φ hΦ hΦ hΦ0 hΦ0 ha hb haa hba (B := univ) .univ
  simp only [Measure.restrict_univ] at haid hbid
  have heid : F.form (a - b) (a - b) =
      (∫ x, dp x ^ 2 ∂Γ.measure p) -
        2 * signedIntegralOn (Γ.cross p r) univ (fun x => dp x * dr x) +
        ∫ x, dr x ^ 2 ∂Γ.measure r := by
    rw [← Γ.cross_univ (a - b) (F.domain.sub_mem ha hb) (a - b) (F.domain.sub_mem ha hb),
      Γ.cross_sub_self_apply ha hb univ, Γ.cross_self a ha univ .univ,
      Γ.cross_self b hb univ .univ, haid, hbid, hcrossid]
  have hfixed : (∫ x, (dp x - dr x) ^ 2 ∂Γ.measure u) =
      (∫ x, dp x ^ 2 ∂Γ.measure u) - 2 * (∫ x, dp x * dr x ∂Γ.measure u) +
        ∫ x, dr x ^ 2 ∂Γ.measure u := by
    have he : (fun x => (dp x - dr x) ^ 2) = fun x => (dp x ^ 2 - 2 * (dp x * dr x)) + dr x ^ 2 := by
      funext x
      ring
    rw [he]
    have hadd := integral_add (hip.sub (hipr.const_mul 2)) hir
    have hsub := integral_sub hip (hipr.const_mul 2)
    simp only [Pi.sub_apply] at hadd hsub
    rw [hadd, hsub, integral_const_mul]
  rw [heid]
  change _ ≤ (∫ x, (dp x - dr x) ^ 2 ∂Γ.measure u) + _ + _
  rw [hfixed]
  have hmp := (abs_le.mp hmeasurep).2
  have hmr := (abs_le.mp hmeasurer).2
  have hmc := (abs_le.mp hcross).1
  linarith

variable [SecondCountableTopology X]

theorem EnergyFamily.quasiContinuous_chain_eq_of_c1 {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    {L : ℝ≥0} (hL : LipschitzWith L Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (q.rep u hu x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal = ∫ x in B, (deriv Φ (q.rep u hu x)) ^ 2 ∂Γ.measure u := by
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
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hL (x₀ := r)
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
      exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using haK n x
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
    · simpa only [mul_zero] using hD0.const_mul (2 * (L : ℝ) ^ 2)
  have hvar : Tendsto (fun n => ∫ x in B, a n x ∂Γ.measure (un (s n))) atTop
      (𝓝 (∫ x in B, a0 x ∂Γ.measure u)) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add hfixed
  have hidentity : ∀ n, (Γ.measure (v n) B).toReal = ∫ x in B, a n x ∂Γ.measure (un (s n)) := by
    intro n
    apply Γ.core_chain h (hun (s n)) (hfn (s n)).1 (hfn (s n)).2.2.2 Φ hΦ hΦ0 (hv n)
    · exact (hL.coeFn_compLp hΦ0 (un (s n))).trans ((hfn (s n)).2.2.2.fun_comp Φ)
    · exact hB
  have hmass : Tendsto (fun n => (Γ.measure (v n) B).toReal) atTop
      (𝓝 (∫ x in B, a0 x ∂Γ.measure u)) := by simpa only [hidentity] using hvar
  let dn : ℕ → X → ℝ := fun n x => deriv Φ (fn (s n) x)
  let d0 : X → ℝ := fun x => deriv Φ (q.rep u hu x)
  have hdn : ∀ n, Measurable (dn n) := fun n =>
    ((hΦ.continuous_deriv le_rfl).comp (hfn (s n)).1).measurable
  have hd0 : Measurable d0 := (hΦ.continuous_deriv le_rfl).measurable.comp (q.measurable u hu)
  have hdnL : ∀ n x, |dn n x| ≤ L := fun n x => hderiv _
  have hd0L : ∀ x, |d0 x| ≤ L := fun x => hderiv _
  let e : ℕ → ℝ := fun n => ∫ x, (dn n x - d0 x) ^ 2 ∂Γ.measure u
  have heBound : ∀ n x, ‖(dn n x - d0 x) ^ 2‖ ≤ 4 * (L : ℝ) ^ 2 := by
    intro n x
    have hh : |dn n x - d0 x| ≤ 2 * (L : ℝ) :=
      (abs_sub _ _).trans (by linarith [hdnL n x, hd0L x])
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc
      _ ≤ (2 * (L : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
      _ = _ := by ring
  have heInt : ∀ n, Integrable (fun x => (dn n x - d0 x) ^ 2) (Γ.measure u) := fun n =>
    (integrable_const (4 * (L : ℝ) ^ 2)).mono'
      (((hdn n).sub hd0).pow_const 2).aestronglyMeasurable (Eventually.of_forall (heBound n))
  have he0 : Tendsto e atTop (𝓝 0) := by
    have hh : ∀ᵐ x ∂Γ.measure u, Tendsto (fun n => (dn n x - d0 x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hsae u hu] with x hx
      have hd := (hΦ.continuous_deriv le_rfl).tendsto (q.rep u hu x) |>.comp hx
      simpa only [dn, d0, Function.comp_def, sub_self, zero_pow two_ne_zero] using (hd.sub_const (d0 x)).pow 2
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun _ : X => 4 * (L : ℝ) ^ 2) (fun n => (heInt n).1)
      (integrable_const _) (fun n => Eventually.of_forall (heBound n)) hh
  let C : ℝ := Real.sqrt (2 * F.form u u + 2) + Real.sqrt (F.form u u)
  have huC : Real.sqrt (F.form u u) ≤ C := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hunC : ∀ n, Real.sqrt (F.form (un (s n)) (un (s n))) ≤ C := fun n =>
    (Real.sqrt_le_sqrt (hbound (s n))).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  let g : ℕ → ℝ := fun n => Real.sqrt (F.form (un (s n) - u) (un (s n) - u))
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hh : Tendsto (fun n => F.form (un (s n) - u) (un (s n) - u)) atTop (𝓝 0) :=
      squeeze_zero (fun n => F.form_nonneg _ (F.domain.sub_mem (hun (s n)).1 hu))
        (fun n => F.form_le_energyNormSq) (henergy.comp hs.tendsto_atTop)
    simpa only [Real.sqrt_zero] using! Real.continuous_sqrt.tendsto 0 |>.comp hh
  let error : ℕ → ℝ := fun n => 2 * e n + 2 * (L : ℝ) ^ 2 * D n + 4 * (L : ℝ) ^ 2 * C * g n
  have herror0 : Tendsto error atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using! ((he0.const_mul 2).add
      (hD0.const_mul (2 * (L : ℝ) ^ 2))).add (hg0.const_mul (4 * (L : ℝ) ^ 2 * C))
  have htriangle : ∀ p r, (∫ x, (dn p x - dn r x) ^ 2 ∂Γ.measure u) ≤ 2 * e p + 2 * e r := by
    intro p r
    have hInt : Integrable (fun x => (dn p x - dn r x) ^ 2) (Γ.measure u) := by
      apply (integrable_const (4 * (L : ℝ) ^ 2)).mono'
        (((hdn p).sub (hdn r)).pow_const 2).aestronglyMeasurable
      apply Eventually.of_forall
      intro x
      have hh : |dn p x - dn r x| ≤ 2 * (L : ℝ) :=
        (abs_sub _ _).trans (by linarith [hdnL p x, hdnL r x])
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      calc
        _ ≤ (2 * (L : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
        _ = _ := by ring
    calc
      _ ≤ ∫ x, 2 * (dn p x - d0 x) ^ 2 + 2 * (dn r x - d0 x) ^ 2 ∂Γ.measure u := by
        apply integral_mono hInt ((heInt p).const_mul 2 |>.add ((heInt r).const_mul 2))
        intro x
        change (dn p x - dn r x) ^ 2 ≤ 2 * (dn p x - d0 x) ^ 2 + 2 * (dn r x - d0 x) ^ 2
        nlinarith [sq_nonneg (dn p x + dn r x - 2 * d0 x)]
      _ = 2 * e p + 2 * e r := by
        rw [integral_add ((heInt p).const_mul 2) ((heInt r).const_mul 2),
          integral_const_mul, integral_const_mul]
  have hgap : ∀ p r, F.form (v p - v r) (v p - v r) ≤ error p + error r := by
    intro p r
    have hbase := Γ.c1_comp_form_sub_le h (hun (s p)) (hun (s r)) hu
      (hfn (s p)).1 (hfn (s r)).1 (hfn (s p)).2.2.2 (hfn (s r)).2.2.2
      Φ hΦ hL hΦ0 (hv p) (hv r)
      ((hL.coeFn_compLp hΦ0 (un (s p))).trans ((hfn (s p)).2.2.2.fun_comp Φ))
      ((hL.coeFn_compLp hΦ0 (un (s r))).trans ((hfn (s r)).2.2.2.fun_comp Φ))
      (hunC r) huC
    change F.form (v p - v r) (v p - v r) ≤
      (∫ x, (dn p x - dn r x) ^ 2 ∂Γ.measure u) + 2 * (L : ℝ) ^ 2 * (D p + D r) +
        4 * (L : ℝ) ^ 2 * C * (g p + g r) at hbase
    calc
      _ ≤ (∫ x, (dn p x - dn r x) ^ 2 ∂Γ.measure u) + 2 * (L : ℝ) ^ 2 * (D p + D r) +
          4 * (L : ℝ) ^ 2 * C * (g p + g r) := hbase
      _ ≤ (2 * e p + 2 * e r) + 2 * (L : ℝ) ^ 2 * (D p + D r) +
          4 * (L : ℝ) ^ 2 * C * (g p + g r) :=
        add_le_add (add_le_add (htriangle p r) le_rfl) le_rfl
      _ = error p + error r := by dsimp only [error]; ring
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      F.form (v p - v r) (v p - v r) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (herror0.eventually (Iio_mem_nhds (half_pos hε)))
    refine ⟨N, fun p hp r hr => (hgap p r).trans_lt ?_⟩
    linarith [hN p hp, hN r hr]
  have hvenergy := F.mem_domain_of_tendsto_of_formCauchy v hv w hvlim hcauchy |>.2
  have htarget := Γ.measure_tendsto_of_energy hv hw hvenergy hB
  exact tendsto_nhds_unique htarget hmass

end DirichletForm.FOTConstruction
