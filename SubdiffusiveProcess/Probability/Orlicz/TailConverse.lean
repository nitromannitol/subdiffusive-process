import Mathlib
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit

/-! Exact converse of the stretched-exponential tail estimate.
The layer-cake argument adapts SubdiffusiveProcess.OGammaBridge to the exact all-level tail hypothesis. -/
open MeasureTheory
noncomputable section
namespace SubdiffusiveProcess.Probability.Orlicz
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_exp_le_two_of_tail {Z : Ω → ℝ} (hZ : ∀ ω, 0 ≤ Z ω)
    (hm : AEMeasurable Z μ)
    (ht : ∀ r : ℝ, 0 < r → μ {ω | r < Z ω} ≤ ENNReal.ofReal (Real.exp (-2 * r))) :
    Integrable (fun ω => Real.exp (Z ω)) μ ∧ (∫ ω, Real.exp (Z ω) ∂μ ≤ 2) := by
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (f := Z) (g := Real.exp) (Filter.Eventually.of_forall hZ) hm
    (fun r _ => Real.continuous_exp.intervalIntegrable 0 r)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have hdom : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      μ {ω | r < Z ω} * ENNReal.ofReal (Real.exp r) ≤ ENNReal.ofReal (Real.exp (-r)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-2 * r)) * ENNReal.ofReal (Real.exp r) :=
        mul_le_mul_left (ht r hr) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring
  have hg : IntegrableOn (fun r : ℝ => Real.exp (-r)) (Set.Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  have hgL : ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-r)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    have hi : ∫ r in Set.Ioi (0 : ℝ), Real.exp (-r) = 1 := by
      simpa using
        integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
    rw [hi, ENNReal.ofReal_one]
  have hL : ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ ≤ 1 := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (∫ r in (0 : ℝ)..Z ω, Real.exp r) ∂μ := by
        apply lintegral_congr
        intro ω
        rw [integral_exp, Real.exp_zero]
      _ = _ := hlayer
      _ ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-r)) := lintegral_mono_ae hdom
      _ = 1 := hgL
  have hpoint : ∀ ω, ENNReal.ofReal (Real.exp (Z ω)) =
      ENNReal.ofReal (Real.exp (Z ω) - 1) + 1 := by
    intro ω
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith [Real.one_le_exp (hZ ω)]) (by norm_num)]
    congr 1
    ring
  have hExpL : ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂μ ≤ ENNReal.ofReal 2 := by
    simp_rw [hpoint]
    rw [lintegral_add_right _ measurable_const]
    have h := add_le_add hL (le_refl (1 : ENNReal))
    simpa only [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_ofNat, one_add_one_eq_two] using h
  have heM := hm.exp.aestronglyMeasurable
  have heN : 0 ≤ᵐ[μ] fun ω => Real.exp (Z ω) := Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have heI : Integrable (fun ω => Real.exp (Z ω)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable heM heN).mp
      (ne_of_lt (hExpL.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨heI, ?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hExpL
  rw [← ofReal_integral_eq_lintegral_ofReal heI heN] at h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae heN), ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using h

lemma ogammaLE_of_all_level_tail {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    (hX : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t * A ≤ X ω} ≤ Real.exp (-(t ^ σ))) :
    SubdiffusiveProcess.OGammaLE μ σ (2 ^ (1 / σ) * A) X := by
  let Y : Ω → ℝ := fun ω => A⁻¹ * max (X ω) 0
  let Z : Ω → ℝ := fun ω => Y ω ^ σ / 2
  have hY : ∀ ω, 0 ≤ Y ω := fun ω => mul_nonneg (inv_nonneg.mpr hA.le) (le_max_right _ _)
  have hZ : ∀ ω, 0 ≤ Z ω := fun ω => div_nonneg (Real.rpow_nonneg (hY ω) _) (by norm_num)
  have hYm : AEMeasurable Y μ := (hXm.max aemeasurable_const).const_mul A⁻¹
  have hZm : AEMeasurable Z μ := (hYm.pow aemeasurable_const).div_const 2
  have ht : ∀ r : ℝ, 0 < r → μ {ω | r < Z ω} ≤ ENNReal.ofReal (Real.exp (-2 * r)) := by
    intro r hr
    let u : ℝ := (2 * r) ^ σ⁻¹
    have hu : 0 < u := Real.rpow_pos_of_pos (by positivity) _
    have hup : u ^ σ = 2 * r := Real.rpow_inv_rpow (by positivity) hσ.ne'
    have hs : {ω | r < Z ω} ⊆ {ω | u * A ≤ X ω} := by
      intro ω hω
      have hpow : u ^ σ < Y ω ^ σ := by rw [hup]; dsimp [Z] at hω; linarith
      have hless : u < Y ω := (Real.rpow_lt_rpow_iff hu.le (hY ω) hσ).mp hpow
      have hmax : u * A < max (X ω) 0 := by
        dsimp [Y] at hless
        rw [inv_mul_eq_div] at hless
        exact (lt_div_iff₀ hA).mp hless
      rcases lt_max_iff.mp hmax with h | h
      · exact h.le
      · exact False.elim (not_lt_of_ge (mul_nonneg hu.le hA.le) h)
    have hb := hX u hu.le
    change μ.real {ω | u * A ≤ X ω} ≤ Real.exp (-(u ^ σ)) at hb
    rw [hup] at hb
    calc
      _ ≤ μ {ω | u * A ≤ X ω} := measure_mono hs
      _ = ENNReal.ofReal (μ.real {ω | u * A ≤ X ω}) := (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [neg_mul] using hb)
  obtain ⟨hi, hb⟩ := integrable_exp_le_two_of_tail hZ hZm ht
  have hc : 0 < (2 : ℝ) ^ (1 / σ) := Real.rpow_pos_of_pos (by norm_num) _
  have heq : ∀ ω, (((2 : ℝ) ^ (1 / σ) * A)⁻¹ * max (X ω) 0) ^ σ = Z ω := by
    intro ω
    have hbase : ((2 : ℝ) ^ (1 / σ) * A)⁻¹ * max (X ω) 0 = Y ω / ((2 : ℝ) ^ (1 / σ)) := by
      dsimp [Y]
      field_simp
    rw [hbase, Real.div_rpow (hY ω) hc.le]
    have hpow : ((2 : ℝ) ^ (1 / σ)) ^ σ = 2 := by
      rw [one_div, Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2) hσ.ne']
    rw [hpow]
  exact ⟨by simpa only [heq] using hi, by simpa only [heq] using hb⟩

end SubdiffusiveProcess.Probability.Orlicz
