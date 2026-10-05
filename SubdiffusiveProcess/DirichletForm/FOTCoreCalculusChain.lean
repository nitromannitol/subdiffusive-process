module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusChainLocal
public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusCover

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal ContDiff

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

theorem square_error_bound {d a ε : ℝ} (hε : 0 ≤ ε) (hd : |d - a| ≤ ε) :
    |d ^ 2 - a ^ 2| ≤ 2 * |a| * ε + ε ^ 2 := by
  have hsum : |d + a| ≤ ε + 2 * |a| := by
    calc
      |d + a| = |(d - a) + 2 * a| := by congr 1; ring
      _ ≤ |d - a| + |2 * a| := abs_add_le _ _
      _ ≤ ε + 2 * |a| := by rw [abs_mul]; norm_num; exact hd
  calc
    |d ^ 2 - a ^ 2| = |d - a| * |d + a| := by rw [← abs_mul]; congr 1; ring
    _ ≤ ε * (ε + 2 * |a|) := mul_le_mul hd hsum (abs_nonneg _) hε
    _ = _ := by ring

/-- The continuous-core chain rule, obtained by locally affine approximation. -/
theorem EnergyFamily.core_chain_formula {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) {uc : X → ℝ}
    (huc : Continuous uc) (huae : ⇑u =ᵐ[m] uc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain) (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x))
    {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal = ∫ x in B, (deriv Φ (uc x)) ^ 2 ∂(Γ.measure u) := by
  classical
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu.1⟩
  let : IsFiniteMeasure (Γ.measure w) := ⟨Γ.finite w hw⟩
  obtain ⟨f, hf, hfc, hfU, hfae⟩ := hu.2
  let K := tsupport f
  have hKu : Γ.measure u Kᶜ = 0 := Γ.measure_compl_tsupport h hu.1 hfae
  have hwf : ⇑w =ᵐ[m] Φ ∘ f := hwae.trans ((huae.symm.trans hfae).fun_comp Φ)
  have hKw : Γ.measure w Kᶜ = 0 := by
    apply le_zero_iff.mp
    exact (measure_mono (compl_subset_compl.mpr (tsupport_comp_subset hΦ0 f))).trans_eq
      (Γ.measure_compl_tsupport h hw hwf)
  have hKae : ∀ᵐ x ∂Γ.measure u, x ∈ K := ae_iff.mpr hKu
  have hrestrict : (Γ.measure u).restrict K = Γ.measure u :=
    Measure.restrict_eq_self_of_ae_mem hKae
  let g : X → ℝ := fun x => (deriv Φ (uc x)) ^ 2
  have hg : Continuous g := ((hΦ.continuous_deriv le_rfl).comp huc).pow 2
  have hgint : Integrable g (Γ.measure u) := by
    have hh := hg.continuousOn.integrableOn_compact (μ := Γ.measure u) hfc
    change Integrable g ((Γ.measure u).restrict K) at hh
    rwa [hrestrict] at hh
  obtain ⟨D₀, hD₀⟩ := hfc.exists_bound_of_continuousOn
    ((hΦ.continuous_deriv le_rfl).comp huc).continuousOn
  let D := max D₀ 0
  have hD : ∀ x ∈ K, |deriv Φ (uc x)| ≤ D := by
    intro x hx
    have hh : |deriv Φ (uc x)| ≤ D₀ := by
      simpa only [Function.comp_apply, Real.norm_eq_abs] using hD₀ x hx
    exact hh.trans (le_max_left _ _)
  have herror : ∀ ε : ℝ, 0 < ε →
      |(Γ.measure w B).toReal - ∫ x in B, g x ∂Γ.measure u| ≤
        2 * (2 * D * ε + ε ^ 2) * (Γ.measure u B).toReal := by
    intro ε hε
    choose O hO hxO hderiv hlocal using
      fun x : K => Γ.local_affine_chain_bound h hu huc huae hΦ hΦ0 hw hwae x.1 hε
    obtain ⟨s, hcover⟩ := hfc.elim_finite_subcover O hO (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩)
    have hl : ∀ x ∈ s, ∀ A : Set X, MeasurableSet A → A ⊆ O x →
        |(Γ.measure w A).toReal - ∫ y in A, g y ∂Γ.measure u| ≤
          (2 * (2 * D * ε + ε ^ 2)) * (Γ.measure u A).toReal := by
      intro x hx A hA hAO
      let a := deriv Φ (uc x.1)
      let C := 2 * |a| * ε + ε ^ 2
      have hi : |a ^ 2 * (Γ.measure u A).toReal - ∫ y in A, g y ∂Γ.measure u| ≤
          C * (Γ.measure u A).toReal := by
        have hi' := norm_integral_le_of_norm_le_const (μ := (Γ.measure u).restrict A)
          (f := fun y => a ^ 2 - g y) (C := C) (by
            filter_upwards [ae_restrict_mem hA] with y hy
            rw [Real.norm_eq_abs, abs_sub_comm]
            exact square_error_bound hε.le (hderiv x y (hAO hy)))
        rw [integral_sub (integrable_const _) hgint.integrableOn, integral_const] at hi'
        simpa only [Real.norm_eq_abs, measureReal_def, Measure.restrict_apply_univ,
          smul_eq_mul, mul_comm] using hi'
      have hCd : C ≤ 2 * D * ε + ε ^ 2 := by
        dsimp [C, a]
        nlinarith only [mul_le_mul_of_nonneg_right (hD x.1 x.2) hε.le]
      calc
        _ = |((Γ.measure w A).toReal - a ^ 2 * (Γ.measure u A).toReal) +
            (a ^ 2 * (Γ.measure u A).toReal - ∫ y in A, g y ∂Γ.measure u)| := by
          congr 1; ring
        _ ≤ |(Γ.measure w A).toReal - a ^ 2 * (Γ.measure u A).toReal| +
            |a ^ 2 * (Γ.measure u A).toReal - ∫ y in A, g y ∂Γ.measure u| := abs_add_le _ _
        _ ≤ C * (Γ.measure u A).toReal + C * (Γ.measure u A).toReal :=
          add_le_add (hlocal x A hA hAO) hi
        _ ≤ _ := by
          nlinarith only [mul_le_mul_of_nonneg_right hCd
            (ENNReal.toReal_nonneg (a := Γ.measure u A))]
    have he := integral_error_on_finite_cover hgint s O (fun x _ => (hO x).measurableSet)
      hl (hB.inter (isClosed_tsupport f).measurableSet) (inter_subset_right.trans hcover)
    have hint : (∫ x in B ∩ K, g x ∂Γ.measure u) = ∫ x in B, g x ∂Γ.measure u := by
      rw [← Measure.restrict_restrict hB, hrestrict]
    rw [measure_inter_conull hKw, measure_inter_conull hKu, hint] at he
    exact he
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ =>
      2 * (2 * D * (1 / ((n : ℝ) + 1)) + (1 / ((n : ℝ) + 1)) ^ 2) *
        (Γ.measure u B).toReal) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (((ht.const_mul (2 * D)).add (ht.pow 2)).const_mul 2).mul_const (Γ.measure u B).toReal
  have hz : |(Γ.measure w B).toReal - ∫ x in B, g x ∂Γ.measure u| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall fun n =>
      herror (1 / ((n : ℝ) + 1)) (by positivity))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

end SubdiffusiveProcess.DirichletForm.FOTConstruction
