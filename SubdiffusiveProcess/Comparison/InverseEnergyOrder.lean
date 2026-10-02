import SubdiffusiveProcess.Lane2.LimitForm
import Mathlib.Tactic

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal

namespace SubdiffusiveProcess.Comparison

/-- Quadratic response order on a dense set extends to every loading. -/
theorem response_le_of_dense {𝓗 : Type*} [NormedAddCommGroup 𝓗]
    [InnerProductSpace ℝ 𝓗] (GE GF : 𝓗 →L[ℝ] 𝓗) (c : ℝ)
    (D : Set 𝓗) (hD : Dense D)
    (h : ∀ f ∈ D, inner ℝ f (GE f) ≤ c * inner ℝ f (GF f)) :
    ∀ f : 𝓗, inner ℝ f (GE f) ≤ c * inner ℝ f (GF f) := by
  have hclosed : IsClosed {f : 𝓗 | inner ℝ f (GE f) ≤ c * inner ℝ f (GF f)} :=
    isClosed_le (continuous_id.inner GE.continuous)
      (continuous_const.mul (continuous_id.inner GF.continuous))
  have hsub := closure_minimal h hclosed
  rw [hD.closure_eq] at hsub
  exact fun f => hsub (Set.mem_univ f)

/-- Order of inverse quadratic responses gives inclusion and order of the dual energies. -/
theorem form_le_of_response_le {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q) (c : ℝ) (hc : 0 < c)
    (hresponse : ∀ f : DomainL2 Q, inner ℝ f (GE f) ≤ c * inner ℝ f (GF f)) :
    limitFormDomain GE ⊆ limitFormDomain GF ∧
      ∀ u ∈ limitFormDomain GE,
        (limitFormEnergy GF u).toReal ≤ c * (limitFormEnergy GE u).toReal := by
  have henergy : ∀ u ∈ limitFormDomain GE,
      limitFormEnergy GF u ≤ ((c * (limitFormEnergy GE u).toReal : ℝ) : EReal) := by
    intro u hu
    have htop : limitFormEnergy GE u ≠ ⊤ := ne_of_lt hu
    have hbot : limitFormEnergy GE u ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg GE u))
    apply iSup_le
    intro f
    have hdual : ((2 * inner ℝ (c⁻¹ • f) u -
        inner ℝ (c⁻¹ • f) (GE (c⁻¹ • f)) : ℝ) : EReal) ≤ limitFormEnergy GE u :=
      le_iSup (fun g : DomainL2 Q =>
        ((2 * inner ℝ g u - inner ℝ g (GE g) : ℝ) : EReal)) (c⁻¹ • f)
    have hdualReal := EReal.toReal_le_toReal hdual (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe, map_smul, inner_smul_left, inner_smul_right,
      conj_trivial] at hdualReal
    have hscaled := mul_le_mul_of_nonneg_left hdualReal hc.le
    have hcalc : c * (c⁻¹ * (2 * inner ℝ f u) -
        c⁻¹ * (c⁻¹ * inner ℝ f (GE f))) =
        2 * inner ℝ f u - c⁻¹ * inner ℝ f (GE f) := by
      field_simp
    have hcalc' : c * (2 * (c⁻¹ * inner ℝ f u) -
        c⁻¹ * (c⁻¹ * inner ℝ f (GE f))) =
        2 * inner ℝ f u - c⁻¹ * inner ℝ f (GE f) := by
      calc
        _ = c * (c⁻¹ * (2 * inner ℝ f u) -
            c⁻¹ * (c⁻¹ * inner ℝ f (GE f))) := by ring
        _ = _ := hcalc
    rw [hcalc'] at hscaled
    have hresponse' : c⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f) := by
      have h := mul_le_mul_of_nonneg_left (hresponse f) (inv_pos.mpr hc).le
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h
    exact EReal.coe_le_coe_iff.mpr ((sub_le_sub_left hresponse' _).trans hscaled)
  constructor
  · intro u hu
    exact lt_of_le_of_lt (henergy u hu) (EReal.coe_lt_top _)
  · intro u hu
    exact EReal.toReal_le_toReal (henergy u hu)
      (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg GF u)))
      (EReal.coe_ne_top _)

/-- An inequality between almost everywhere measurable scalar readouts descends through
a probability-preserving representation. -/
theorem ae_le_of_pullback {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) (field : Ω → X)
    (hfield : MeasurePreserving field P μ) (f g : X → ℝ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ᵐ ω ∂P, f (field ω) ≤ g (field ω)) : ∀ᵐ x ∂μ, f x ≤ g x := by
  have hmk : ∀ᵐ ω ∂P, hf.mk f (field ω) ≤ hg.mk g (field ω) := by
    filter_upwards [h, hfield.quasiMeasurePreserving.ae hf.ae_eq_mk,
      hfield.quasiMeasurePreserving.ae hg.ae_eq_mk] with ω hw he hf'
    simpa only [← he, ← hf'] using hw
  have hmeas : MeasurableSet {x | hf.mk f x ≤ hg.mk g x} :=
    measurableSet_le hf.measurable_mk hg.measurable_mk
  have hmk' : ∀ᵐ x ∂μ, hf.mk f x ≤ hg.mk g x := by
    have hmap := (ae_map_iff hfield.measurable.aemeasurable hmeas).mpr hmk
    simpa only [hfield.map_eq] using hmap
  filter_upwards [hmk', hf.ae_eq_mk, hg.ae_eq_mk] with x hx he hf'
  simpa only [he, hf'] using hx

end SubdiffusiveProcess.Comparison
