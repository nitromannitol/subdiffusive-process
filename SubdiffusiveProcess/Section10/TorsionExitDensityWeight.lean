import SubdiffusiveProcess.Section10.TorsionExitDriftRegularity

/-! Changing the reference measure of an actual every-start killed density.
The law and its clock are fixed. Division by the original positive speed
coefficient gives the precise density required by the physical consumer. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.Probability.Diffusion.Input
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- The unit speed measure is the original Lebesgue volume. -/
theorem speedMeasure_one {d : ℕ} :
    speedMeasure (fun _ : Vec d ↦ (1 : ℝ)) = volume := by
  simp only [speedMeasure, ENNReal.ofReal_one]
  exact withDensity_one

/-- A Lebesgue killed density becomes `q(t,x,y)/a(y)` against the original
speed measure. Every starting-point identity and joint continuity is preserved. -/
theorem continuousKilledDensities_change_speed {d : ℕ}
    {law : Kernel (Vec d) (LifetimePath (Vec d))} {a : Vec d → ℝ}
    (ha : Continuous a) (hapos : ∀ x, 0 < a x)
    (hdens : ContinuousKilledDensities (fun _ ↦ 1) law) :
    ContinuousKilledDensities a law := by
  intro U hU hUb
  obtain ⟨q, hmeas, hnonneg, hmass, hcont⟩ := hdens U hU hUb
  let p : ℝ → Vec d → Vec d → ℝ := fun t x y ↦ q t x y / a y
  have hpmeas : ∀ t > 0, Measurable (Function.uncurry (p t)) := by
    intro t ht
    exact (hmeas t ht).div (ha.measurable.comp measurable_snd)
  refine ⟨p, hpmeas, ?_, ?_, ?_⟩
  · intro t ht x hx y hy
    exact div_nonneg (hnonneg t ht x hx y hy) (hapos y).le
  · intro t ht x hx B hB
    rw [hmass t ht x hx B hB, speedMeasure_one]
    symm
    change (∫⁻ y in B ∩ U, ENNReal.ofReal (p t x y)
      ∂volume.withDensity (fun y ↦ ENNReal.ofReal (a y))) = _
    have hpy : Measurable (fun y ↦ ENNReal.ofReal (p t x y)) :=
      ((hpmeas t ht).comp measurable_prodMk_left).ennreal_ofReal
    rw [setLIntegral_withDensity_eq_setLIntegral_mul _
      ha.measurable.ennreal_ofReal hpy (hB.inter hU.measurableSet)]
    apply lintegral_congr
    intro y
    change ENNReal.ofReal (a y) * ENNReal.ofReal (q t x y / a y) = _
    rw [← ENNReal.ofReal_mul (hapos y).le, mul_div_cancel₀ _ (hapos y).ne']
  · exact hcont.div
      (ha.comp (continuous_snd.comp continuous_snd)).continuousOn
      (fun z _ ↦ (hapos z.2.2).ne')

end SubdiffusiveProcess.Section10
