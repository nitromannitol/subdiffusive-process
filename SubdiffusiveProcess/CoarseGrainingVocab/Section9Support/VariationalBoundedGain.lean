module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalFiniteGain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalGreenEndpoint

@[expose] public section

/-!
# The Green gain family for bounded forcing

The critical gain supplies the qualitative bound used to justify all
power tests. No bound on the Green solution is assumed in this family,
and the size of the forcing's L infinity norm is absent from its estimate.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Bounded forcing gives a qualitative almost-everywhere bound on the Green solution. -/
theorem variational_green_bounded_of_bounded_forcing {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) {c rho : Vec d → ℝ}
    (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {p0 A F : ℝ} (hp0 : 2 < p0) (hA : 0 < A) (hF : 0 < F)
    (hSob : SobolevAssumption c rho U p0 A F)
    (hPoi : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (hf : MemLp f ⊤ ((weightedMeasure rho).restrict U))
    (u : H10Function U) (hu : IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume.restrict U, |u.toH1Function.toFun x| ≤ M := by
  let mu := (weightedMeasure rho).restrict U
  let : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  obtain ⟨lo, hi, hlo, hrb⟩ := hr.2
  have hmeasure := weightedMeasure_restrict_le_smul_volume_restrict hU.isOpen.measurableSet hi
    (hrb.mono fun _ hx => hx.2)
  let : IsFiniteMeasure mu := ⟨by
    apply (Measure.le_iff.mp hmeasure univ MeasurableSet.univ).trans_lt
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top (volume.restrict U) univ)⟩
  have hfcrit : MemLp f (ENNReal.ofReal (2 / (1 - 2 / p0))) mu := hf.mono_exponent le_top
  have h := variational_green_critical_gain hU hne hc hr hp0 hA hF hSob hPoi hfcrit u hu
  have hmass : mu univ = weightedMeasure rho U := by simp only [mu, Measure.restrict_apply_univ]
  have hmu0 : 0 < mu univ := weightedMeasure_restrict_open_pos hU.isOpen hr univ isOpen_univ
    (by simpa only [univ_inter] using hne)
  have hM0 : weightedMeasure rho U ≠ 0 := by rw [← hmass]; exact hmu0.ne'
  have hMt : weightedMeasure rho U ≠ ⊤ := by rw [← hmass]; exact measure_ne_top mu univ
  have hpower : weightedMeasure rho U ^ (-(1 - 2 / p0) / 2) ≠ ⊤ := by
    intro hx
    rcases ENNReal.rpow_eq_top_iff.mp hx with hz | htop
    · exact hM0 hz.1
    · exact hMt htop.1
  have htop : eLpNorm u.toH1Function.toFun ⊤ mu ≠ ⊤ :=
    (h.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpower.lt_top)
      hfcrit.eLpNorm_lt_top)).ne
  have hae : ∀ᵐ x ∂mu, |u.toH1Function.toFun x| ≤ (eLpNorm u.toH1Function.toFun ⊤ mu).toReal := by
    filter_upwards [ae_le_eLpNormEssSup (f := u.toH1Function.toFun) (μ := mu)] with x hx
    have hmeas := (show MemLp u.toH1Function.toFun ∞ mu from lt_top_iff_ne_top.mpr htop).aestronglyMeasurable
    rw [← eLpNorm_exponent_top hmeas] at hx
    have hrx := ENNReal.toReal_mono htop hx
    simpa only [← ofReal_norm, Real.norm_eq_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using! hrx
  exact ⟨_, ENNReal.toReal_nonneg,
    hae.filter_mono (Measure.AbsolutelyContinuous.ae_le
      (volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.isOpen.measurableSet hr))⟩

/-- Signed finite-exponent Green gains. The forcing is allowed any finite
input exponent in the Sobolev range, with boundedness used only qualitatively. -/
theorem variational_green_finite_gain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) {c rho : Vec d → ℝ}
    (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {p0 p q A F : ℝ} (hp0 : 2 < p0) (hp : 1 < p) (hq : p0 ≤ q)
    (hgain : 1 / p - 1 / q ≤ 1 - 2 / p0)
    (hA : 0 < A) (hF : 0 < F)
    (hSob : SobolevAssumption c rho U p0 A F)
    (hPoi : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (hf : MemLp f ⊤ ((weightedMeasure rho).restrict U))
    (u : H10Function U) (hu : IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f) :
    eLpNorm u.toH1Function.toFun (ENNReal.ofReal q) ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal (2 * A * (A + 1) * F * ((q / p0) ^ 2 / (2 * (q / p0) - 1))) *
        weightedMeasure rho U ^ (1 / q - 1 / p) *
          eLpNorm f (ENNReal.ofReal p) ((weightedMeasure rho).restrict U) := by
  have hp00 : 0 < p0 := by linarith
  have hq0 : 0 < q := hp00.trans_le hq
  have hs : 1 ≤ q / p0 := (le_div_iff₀ hp00).mpr (by simpa using hq)
  have heq : p0 * (q / p0) = q := by field_simp
  have hbalance : 1 / p + (2 * (q / p0) - 1) / (p0 * (q / p0)) ≤ 1 := by
    rw [heq]
    have hfrac : (2 * (q / p0) - 1) / q = 2 / p0 - 1 / q := by field_simp
    rw [hfrac]
    linarith
  obtain ⟨M, hM, hub⟩ := variational_green_bounded_of_bounded_forcing hU hne hc hr hp0 hA hF hSob hPoi hf u hu
  have hpos := variational_green_positive_finite_gain hU hne hc hr hp0 hp hs hbalance hA.le hF.le
    hSob hPoi hf.aestronglyMeasurable u hu hM hub
  have hubneg : ∀ᵐ x ∂volume.restrict U, |(-u).toH1Function.toFun x| ≤ M := by
    filter_upwards [hub] with x hx
    change |(-1 : ℝ) * u.toH1Function.toFun x| ≤ M
    simpa only [neg_one_mul, abs_neg] using hx
  have hneg := variational_green_positive_finite_gain hU hne hc hr hp0 hp hs hbalance hA.le hF.le
    hSob hPoi (hf.neg.aestronglyMeasurable) (-u) (isMassiveWeakSolutionOn_neg hu) hM hubneg
  have hnegfun : (fun x => max ((-u).toH1Function.toFun x) 0) =
      fun x => max (-u.toH1Function.toFun x) 0 := by
    funext x
    change max ((-1 : ℝ) * u.toH1Function.toFun x) 0 = _
    rw [neg_one_mul]
  rw [heq] at hpos hneg
  rw [hnegfun, eLpNorm_neg] at hneg
  have hum : AEStronglyMeasurable u.toH1Function.toFun ((weightedMeasure rho).restrict U) :=
    (memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr u.toH1Function.memL2).aestronglyMeasurable
  have hsplit : u.toH1Function.toFun =
      (fun x => max (u.toH1Function.toFun x) 0) - (fun x => max (-u.toH1Function.toFun x) 0) := by
    funext x
    simp only [Pi.sub_apply]
    rcases le_total 0 (u.toH1Function.toFun x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_sub, neg_neg]
  have htri := eLpNorm_sub_le (μ := (weightedMeasure rho).restrict U)
    (f := fun x => max (u.toH1Function.toFun x) 0)
    (g := fun x => max (-u.toH1Function.toFun x) 0)
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal q from by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ q))
  rw [hsplit]
  refine htri.trans ((add_le_add hpos hneg).trans_eq ?_)
  have hB : 0 ≤ A * (A + 1) * F * ((q / p0) ^ 2 / (2 * (q / p0) - 1)) := by
    have ht : 0 < 2 * (q / p0) - 1 := by linarith
    positivity
  rw [show 2 * A * (A + 1) * F * ((q / p0) ^ 2 / (2 * (q / p0) - 1)) =
      A * (A + 1) * F * ((q / p0) ^ 2 / (2 * (q / p0) - 1)) +
      A * (A + 1) * F * ((q / p0) ^ 2 / (2 * (q / p0) - 1)) by ring,
    ENNReal.ofReal_add hB hB]
  ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
