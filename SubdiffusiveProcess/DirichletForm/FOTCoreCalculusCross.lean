module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusCrossLocal
public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusCrossCover

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal ContDiff

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

/-- The polarized core chain rule, by simultaneous local affine approximation. -/
theorem EnergyFamily.core_cross_chain_formula {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) (hv : F.toClosedForm.MemCoreOn U v)
    {uc vc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    (Φ Ψ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) (hΨ : ContDiff ℝ 1 Ψ)
    (hΦ0 : Φ 0 = 0) (hΨ0 : Ψ 0 = 0)
    {w z : Lp ℝ 2 m} (hw : w ∈ F.domain) (hz : z ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x)) (hzae : ⇑z =ᵐ[m] fun x => Ψ (vc x))
    {B : Set X} (hB : MeasurableSet B) :
    Γ.cross w z B = _root_.DirichletForm.signedIntegralOn (Γ.cross u v) B
      (fun x => deriv Φ (uc x) * deriv Ψ (vc x)) := by
  classical
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu.1⟩
  letI : IsFiniteMeasure (Γ.measure v) := ⟨Γ.finite v hv.1⟩
  let μ := Γ.measure u + Γ.measure v
  let ρ := Γ.cross u v
  let ν := Γ.cross w z
  let g : X → ℝ := fun x => deriv Φ (uc x) * deriv Ψ (vc x)
  have hg : Continuous g := ((hΦ.continuous_deriv le_rfl).comp huc).mul
    ((hΨ.continuous_deriv le_rfl).comp hvc)
  obtain ⟨f, hf, hfc, hfU, hfae⟩ := hu.2
  let K := tsupport f
  have hKu : Γ.measure u Kᶜ = 0 := Γ.measure_compl_tsupport h hu.1 hfae
  have hwf : ⇑w =ᵐ[m] Φ ∘ f := hwae.trans ((huae.symm.trans hfae).fun_comp Φ)
  have hKw : Γ.measure w Kᶜ = 0 := by
    apply le_zero_iff.mp
    exact (measure_mono (compl_subset_compl.mpr (tsupport_comp_subset hΦ0 f))).trans_eq
      (Γ.measure_compl_tsupport h hw hwf)
  have hKρ : ρ.totalVariation Kᶜ = 0 := (Γ.cross_variation_ac_left hu.1 hv.1) hKu
  have hKν : ν.totalVariation Kᶜ = 0 := (Γ.cross_variation_ac_left hw hz) hKw
  have hgint : SignedIntegrable ρ g := signedIntegrable_of_compact_carrier ρ hfc hKρ hg
  obtain ⟨D₀, hD₀⟩ := hfc.exists_bound_of_continuousOn
    ((hΦ.continuous_deriv le_rfl).comp huc).continuousOn
  obtain ⟨E₀, hE₀⟩ := hfc.exists_bound_of_continuousOn
    ((hΨ.continuous_deriv le_rfl).comp hvc).continuousOn
  let D := max D₀ 0
  let E := max E₀ 0
  have hD : ∀ x ∈ K, |deriv Φ (uc x)| ≤ D := by
    intro x hx
    have hh : |deriv Φ (uc x)| ≤ D₀ := by simpa only [Function.comp_apply, Real.norm_eq_abs] using hD₀ x hx
    exact hh.trans (le_max_left _ _)
  have hE : ∀ x ∈ K, |deriv Ψ (vc x)| ≤ E := by
    intro x hx
    have hh : |deriv Ψ (vc x)| ≤ E₀ := by simpa only [Function.comp_apply, Real.norm_eq_abs] using hE₀ x hx
    exact hh.trans (le_max_left _ _)
  let T : Set X → ℝ := fun A => ν A - _root_.DirichletForm.signedIntegralOn ρ A g
  have hT0 : T ∅ = 0 := by simp [T, _root_.DirichletForm.signedIntegralOn]
  have hTadd : ∀ A C : Set X, MeasurableSet A → MeasurableSet C → Disjoint A C →
      T (A ∪ C) = T A + T C := by
    intro A C hA hC hAC
    simp only [T, ν.of_union hAC hA hC, signedIntegralOn_union ρ hgint hA hC hAC]
    ring
  have herror : ∀ ε : ℝ, 0 < ε → |T B| ≤ 2 * ε * (D + E + ε) * (μ B).toReal := by
    intro ε hε
    choose O₁ hO₁ hxO₁ hd₁ hlocal₁ using fun x : K =>
      Γ.local_affine_chain_bound h hu huc huae hΦ hΦ0 hw hwae x.1 hε
    choose O₂ hO₂ hxO₂ hd₂ hlocal₂ using fun x : K =>
      Γ.local_affine_chain_bound h hv hvc hvae hΨ hΨ0 hz hzae x.1 hε
    let O : K → Set X := fun x => O₁ x ∩ O₂ x
    have hO : ∀ x, IsOpen (O x) := fun x => (hO₁ x).inter (hO₂ x)
    obtain ⟨s, hcover⟩ := hfc.elim_finite_subcover O hO (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxO₁ ⟨x, hx⟩, hxO₂ ⟨x, hx⟩⟩)
    have hl : ∀ x ∈ s, ∀ A : Set X, MeasurableSet A → A ⊆ O x →
        |T A| ≤ (2 * ε * (D + E + ε)) * (μ A).toReal := by
      intro x hx A hA hAO
      let a := deriv Φ (uc x.1)
      let b := deriv Ψ (vc x.1)
      let C := ε * (|a| + |b| + ε)
      have hCn : 0 ≤ C := mul_nonneg hε.le
        (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hε.le)
      have hdb : (Γ.measure (w - a • u) A).toReal ≤ ε ^ 2 * (Γ.measure u A).toReal :=
        Γ.composition_difference_bound h hu huc huae hΦ hΦ0 hw hwae a hε.le hA
          (fun y hy => hd₁ x y (hAO hy).1)
      have heb : (Γ.measure (z - b • v) A).toReal ≤ ε ^ 2 * (Γ.measure v A).toReal :=
        Γ.composition_difference_bound h hv hvc hvae hΨ hΨ0 hz hzae b hε.le hA
          (fun y hy => hd₂ x y (hAO hy).2)
      have he1 : |ν A - a * b * ρ A| ≤ C * (μ A).toReal := by
        have hh := Γ.cross_affine_error hu.1 hv.1 hw hz hε.le hA hdb heb
        simpa only [μ, Measure.add_apply, ENNReal.toReal_add (Γ.measure_ne_top hu.1 A)
          (Γ.measure_ne_top hv.1 A), C, ν, ρ, a, b] using hh
      have hgc : SignedIntegrable ρ (fun _ => -(a * b)) := ⟨integrable_const _, integrable_const _⟩
      have hrewrite : _root_.DirichletForm.signedIntegralOn ρ A (fun y => g y - a * b) =
          _root_.DirichletForm.signedIntegralOn ρ A g - a * b * ρ A := by
        have hh := signedIntegralOn_add ρ hgint hgc A
        simp only [signedIntegralOn_const ρ hA, neg_mul] at hh
        simpa only [sub_eq_add_neg] using hh
      have he2 : |a * b * ρ A - _root_.DirichletForm.signedIntegralOn ρ A g| ≤ C * (μ A).toReal := by
        have hh := abs_signedIntegralOn_le ρ hA (f := fun y => g y - a * b) (C := C)
          (fun y hy => product_error_bound hε.le (hd₁ x y (hAO hy).1) (hd₂ x y (hAO hy).2))
        rw [hrewrite, abs_sub_comm] at hh
        apply hh.trans
        exact mul_le_mul_of_nonneg_left
          (ENNReal.toReal_mono (_root_.MeasureTheory.measure_ne_top μ A)
            (Measure.le_iff'.mp (Γ.cross_variation_le hu.1 hv.1) A)) hCn
      have hCd : C ≤ ε * (D + E + ε) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hD x.1 x.2) (hE x.1 x.2)) (le_refl _)) hε.le
      calc
        |T A| = |(ν A - a * b * ρ A) +
            (a * b * ρ A - _root_.DirichletForm.signedIntegralOn ρ A g)| := by
          dsimp only [T]; congr 1; ring
        _ ≤ |ν A - a * b * ρ A| + |a * b * ρ A - _root_.DirichletForm.signedIntegralOn ρ A g| :=
          abs_add_le _ _
        _ ≤ C * (μ A).toReal + C * (μ A).toReal := add_le_add he1 he2
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hCd (ENNReal.toReal_nonneg (a := μ A))]
    have he := additive_error_on_finite_cover T hT0 hTadd s O (fun x _ => (hO x).measurableSet)
      hl (hB.inter (isClosed_tsupport f).measurableSet) (inter_subset_right.trans hcover)
    have hTK : T (B ∩ K) = T B := by
      dsimp only [T]
      rw [signed_apply_inter_carrier ν (isClosed_tsupport f).measurableSet hB hKν,
        signedIntegralOn_inter_carrier ρ (isClosed_tsupport f).measurableSet hB hKρ]
    rw [hTK] at he
    apply he.trans
    exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (_root_.MeasureTheory.measure_ne_top μ B) (measure_mono inter_subset_left))
      (by dsimp [D, E]; positivity)
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) *
      (D + E + 1 / ((n : ℝ) + 1)) * (μ B).toReal) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      ((ht.const_mul 2).mul (tendsto_const_nhds.add ht)).mul_const (μ B).toReal
  have hzT : |T B| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Eventually.of_forall fun n => herror (1 / ((n : ℝ) + 1)) (by positivity))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hzT)

end DirichletForm.FOTConstruction
