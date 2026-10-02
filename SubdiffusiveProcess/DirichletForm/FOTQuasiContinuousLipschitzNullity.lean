import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousLipschitzPrimitives
import SubdiffusiveProcess.DirichletForm.FOTDomainHilbert

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}

/-- Polarizing the C¹ rule gives the integral of a first derivative. -/
theorem EnergyFamily.quasiContinuous_first_derivative
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U)
    (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {L : ℝ≥0}
    (hL : LipschitzWith L Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (q.rep u hu x)) :
    F.form u w = ∫ x, deriv Φ (q.rep u hu x) ∂Γ.measure u := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  let d : X → ℝ := fun x => deriv Φ (q.rep u hu x)
  have hdmeas : Measurable d :=
    (hΦ.continuous_deriv (by norm_num)).measurable.comp (q.measurable u hu)
  have hdint : Integrable d (Γ.measure u) := by
    apply (integrable_const (L : ℝ)).mono' hdmeas.aestronglyMeasurable
    exact Eventually.of_forall fun x => norm_deriv_le_of_lipschitz hL
  have hd2int : Integrable (fun x => d x ^ 2) (Γ.measure u) := by
    apply (integrable_const ((L : ℝ) ^ 2)).mono' (hdmeas.pow_const 2).aestronglyMeasurable
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [Real.norm_eq_abs] using
        (norm_deriv_le_of_lipschitz hL : ‖deriv Φ (q.rep u hu x)‖ ≤ L)) 2
  have haddrep : ⇑(u + w) =ᵐ[m] fun x => q.rep u hu x + Φ (q.rep u hu x) := by
    filter_upwards [Lp.coeFn_add u w, q.ae_rep u hu, hwae] with x h1 h2 h3
    simp only [h1, Pi.add_apply, h2, h3]
  have hΦadd : ContDiff ℝ 1 (fun s => s + Φ s) := contDiff_id.add hΦ
  have hderiv : ∀ s, deriv (fun t => t + Φ t) s = 1 + deriv Φ s := by
    intro s
    exact ((hasDerivAt_id s).add
      ((hΦ.differentiable (by norm_num)) s).hasDerivAt).deriv
  have hchain := Γ.quasiContinuous_chain h q hu Φ hΦ hL hΦ0 hw hwae MeasurableSet.univ
  have hadd := Γ.quasiContinuous_chain h q hu (fun s => s + Φ s) hΦadd
    (LipschitzWith.id.add hL) (by simp only [hΦ0, zero_add])
    (F.domain.add_mem hu hw) haddrep MeasurableSet.univ
  simp only [Measure.restrict_univ, Γ.mass w hw] at hchain
  simp only [Measure.restrict_univ, Γ.mass (u + w) (F.domain.add_mem hu hw), hderiv] at hadd
  have hexpand : (∫ x, (1 + d x) ^ 2 ∂Γ.measure u) =
      F.form u u + 2 * (∫ x, d x ∂Γ.measure u) + (∫ x, d x ^ 2 ∂Γ.measure u) := by
    calc
      _ = ∫ x, (1 : ℝ) + 2 * d x + d x ^ 2 ∂Γ.measure u := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        change (∫ x, (((fun _ : X => (1 : ℝ)) + (fun x => 2 * d x)) +
          (fun x => d x ^ 2)) x ∂Γ.measure u) = _
        rw [integral_add' ((integrable_const 1).add (hdint.const_mul 2)) hd2int,
          integral_add' (integrable_const 1) (hdint.const_mul 2), integral_const_mul,
          integral_const, smul_eq_mul, mul_one, measureReal_def, Γ.mass u hu]
  have hform : F.form (u + w) (u + w) = F.form u u + 2 * F.form u w + F.form w w := by
    rw [F.form_add_left u hu w hw (u + w) (F.domain.add_mem hu hw),
      F.form_add_right hu hu hw, F.form_add_right hw hu hw,
      F.form_symm w hw u hu]
    ring
  change F.form (u + w) (u + w) = ∫ x, (1 + d x) ^ 2 ∂Γ.measure u at hadd
  change F.form w w = ∫ x, d x ^ 2 ∂Γ.measure u at hchain
  rw [hexpand, hform, hchain] at hadd
  change F.form u w = ∫ x, d x ∂Γ.measure u
  linarith

end DirichletForm.FOTConstruction
