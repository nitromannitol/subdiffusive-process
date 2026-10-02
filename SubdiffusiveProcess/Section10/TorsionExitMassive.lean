import SubdiffusiveProcess.Section10.TorsionBound
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumRepresentative

/-! A nonnegative mass can be dropped in positive-level testing. This gives
exactly the torsion cap for the unnormalized discounted unit occupation. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal
namespace SubdiffusiveProcess.Section10

/-- The actual massive equation supplies the pure torsion level estimate. -/
theorem massiveTorsion_positive_level_bound {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {A b : Vec d → ℝ}
    (hb : CoefficientOn U b) {mu p Ksob : ℝ} (hmu : 0 ≤ mu)
    (hKsob : 0 ≤ Ksob) (hSob : TorsionSobolevBound A b U p Ksob)
    {f : Vec d → ℝ} (u : H10Function U)
    (hu : IsMassiveWeakSolutionOn A b mu U u.toH1Function f) :
    ∀ h : ℝ, 0 ≤ h →
      (eLpNorm (fun x => max (u.toFun x - h) 0) (ENNReal.ofReal p)
        ((weightedMeasure b).restrict U)) ^ 2 ≤
      ENNReal.ofReal Ksob * ∫⁻ x, ENNReal.ofReal (|f x| * max (u.toFun x - h) 0)
        ∂(weightedMeasure b).restrict U := by
  intro h hh
  obtain ⟨v, hvf, hvg⟩ := exists_h10_positivePart hU u hh
  have hv0 (x : Vec d) : 0 ≤ v.toFun x := by rw [hvf x]; exact le_max_right _ _
  have hb0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ b x := by
    obtain ⟨lo, hi, hlo, hbounds⟩ := hb.2
    exact hbounds.mono fun x hx => hlo.le.trans hx.1
  have hmass : 0 ≤ ∫ x in U, b x * u.toFun x * v.toFun x := by
    apply integral_nonneg_of_ae
    filter_upwards [hb0] with x hx
    rw [hvf x]
    by_cases hu : u.toFun x ≤ h
    · rw [max_eq_right (sub_nonpos.mpr hu)]; simp
    · exact mul_nonneg (mul_nonneg hx (hh.trans (le_of_not_ge hu))) (le_max_right _ _)
  have htest := hu v
  rw [positivePart_energy_eq hvg] at htest
  have henergyLe : energy A U v.toH1Function ≤
      ∫ x, f x * v.toFun x ∂(weightedMeasure b).restrict U := by
    rw [integral_weightedMeasure_restrict_eq hU.isOpen.measurableSet b _ hb]
    have hmass' : 0 ≤ mu * ∫ x in U, b x * u.toFun x * v.toFun x := mul_nonneg hmu hmass
    simp only [mul_assoc] at htest hmass' ⊢
    linarith
  have henergy : ENNReal.ofReal (energy A U v.toH1Function) ≤
      ∫⁻ x, ENNReal.ofReal (|f x| * v.toFun x) ∂(weightedMeasure b).restrict U := by
    calc
      _ ≤ ENNReal.ofReal (∫ x, f x * v.toFun x ∂(weightedMeasure b).restrict U) :=
        ENNReal.ofReal_le_ofReal henergyLe
      _ ≤ ‖∫ x, f x * v.toFun x ∂(weightedMeasure b).restrict U‖ₑ := by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖f x * v.toFun x‖ₑ ∂(weightedMeasure b).restrict U :=
        enorm_integral_le_lintegral_enorm _
      _ = _ := by
        apply lintegral_congr
        intro x
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 x)]
  have hs := hSob v
  rw [ENNReal.ofReal_mul hKsob] at hs
  have hp := hs.trans (mul_le_mul_right henergy (ENNReal.ofReal Ksob))
  have hvfun : v.toFun = fun x => max (u.toFun x - h) 0 := funext hvf
  change (eLpNorm v.toFun (ENNReal.ofReal p) ((weightedMeasure b).restrict U)) ^ 2 ≤ _ at hp
  simpa only [hvfun] using hp

/-- Unit forcing has the same cap for every nonnegative mass. -/
theorem massiveTorsion_ae_le {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hb : CoefficientOn U b)
    {mu p Ksob : ℝ} (hmu : 0 ≤ mu) (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (u : H10Function U)
    (hu : IsMassiveWeakSolutionOn A b mu U u.toH1Function (fun _ => 1)) :
    ∀ᵐ x ∂(weightedMeasure b).restrict U, u.toFun x ≤
      torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p) := by
  let μ := (weightedMeasure b).restrict U
  letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  letI : IsFiniteMeasure μ := variational_weighted_isFiniteMeasure hU.isOpen.measurableSet hb
  have hM : 0 < (μ univ).toReal := ENNReal.toReal_pos
    (weightedMeasure_restrict_open_pos hU.isOpen hb univ isOpen_univ
      (by simpa only [univ_inter] using hne)).ne' (measure_ne_top μ univ)
  have hu2 : MemLp u.toFun 2 μ :=
    memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hb u.toH1Function.memL2
  have hlevel := massiveTorsion_positive_level_bound hU hb hmu hKsob.le hSob u hu
  have hlevel' : ∀ h : ℝ, 0 ≤ h →
      (eLpNorm (fun x => max (u.toFun x - h) 0) (ENNReal.ofReal p) μ) ^ 2 ≤
      ENNReal.ofReal Ksob * ∫⁻ x, ENNReal.ofReal (max (u.toFun x - h) 0) ∂μ := by
    simpa only [abs_one, one_mul] using hlevel
  simpa only [μ, Measure.restrict_apply_univ] using
    torsion_ae_le_of_level_estimates μ hp hKsob hM hu2 hlevel'

/-- Multiplication by s removes the normalized forcing, without changing A or b. -/
theorem normalizedResolvent_scaled_equation {d : ℕ} {U : Set (Vec d)}
    {A b : Vec d → ℝ} {s : ℝ} (hs : 0 < s) (u : H10Function U)
    (hu : IsMassiveWeakSolutionOn A b s⁻¹ U u.toH1Function (fun _ => s⁻¹)) :
    IsMassiveWeakSolutionOn A b s⁻¹ U (s • u).toH1Function (fun _ => 1) := by
  have h := IsMassiveWeakSolutionOn.const_smul s hu
  simpa only [mul_inv_cancel₀ hs.ne'] using h



end SubdiffusiveProcess.Section10
