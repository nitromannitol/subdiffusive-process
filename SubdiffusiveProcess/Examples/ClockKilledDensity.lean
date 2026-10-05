module

public import SubdiffusiveProcess.Examples.ClockFiniteDistributions
public import SubdiffusiveProcess.Section10.TorsionExitDensityTransport
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
public import MarkovProcess.Killed.Kernel

@[expose] public section

/-! # Every-start killed-density transport through a positive constant clock -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Examples
noncomputable section



theorem continuous_lifetime_killedEvent {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (t : ℝ) (x : Fin d → ℝ)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    (K.map LifetimePath.ofContinuousPath) x
      {w | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
        LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} =
      K x (ContinuousPath.killedEvent U (Real.toNNReal t) B) := by
  have hcoord : MeasurableSet (Cemetery.alive '' B) := measurableSet_inl_image.mpr hB
  have hevent : MeasurableSet
      {w : LifetimePath (Fin d → ℝ) | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
        LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} :=
    (measurableSet_lt measurable_const
      (LifetimePath.isStoppingTime_exitTime U hU).measurable').inter
      ((LifetimePath.measurable_coordinate (Real.toNNReal t)) hcoord)
  rw [Kernel.map_apply' K LifetimePath.measurable_ofContinuousPath x hevent]
  congr 1
  ext w
  simp only [mem_preimage, mem_ofPred_eq, LifetimePath.exitTime_ofContinuousPath,
    LifetimePath.coordinate_ofContinuousPath, ContinuousPath.mem_killedEvent_iff]
  constructor
  · rintro ⟨ht, z, hz, heq⟩
    exact ⟨ht, (Sum.inl.inj heq) ▸ hz⟩
  · rintro ⟨ht, hw⟩
    exact ⟨ht, w (Real.toNNReal t), hw, rfl⟩

/-- The exact killed endpoint event has the multiplied original time. -/
theorem clockKernel_killedEvent {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (c : NNReal) (hc : 0 < c) {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (t : NNReal) (x : Fin d → ℝ) {B : Set (Fin d → ℝ)} (hB : MeasurableSet B) :
    clockKernel K c x (ContinuousPath.killedEvent U t B) =
      K x (ContinuousPath.killedEvent U (c * t) B) := by
  rw [clockKernel, Kernel.map_apply' _ (ContinuousPath.measurable_rescale _ _) x
    (ContinuousPath.measurableSet_killedEvent U hU t hB)]
  congr 1
  ext w
  simp only [mem_preimage, ContinuousPath.mem_killedEvent_iff]
  have h := SubdiffusiveProcess.Section10.lt_exitTime_rescale_iff (Homeomorph.refl (Fin d → ℝ)) c hc hU t w
  simp only [Homeomorph.refl_symm, Homeomorph.refl_apply, Set.image_id] at h
  exact and_congr_left fun _ => h

/-- Multiply time in the density while retaining the identical speed measure. -/
theorem clockKernel_continuousKilledDensities {d : ℕ}
    (rho : (Fin d → ℝ) → ℝ)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (hD : SubdiffusiveProcess.Probability.Diffusion.Input.ContinuousKilledDensities rho
      (K.map LifetimePath.ofContinuousPath)) (c : NNReal) (hc : 0 < c) :
    SubdiffusiveProcess.Probability.Diffusion.Input.ContinuousKilledDensities rho
      ((clockKernel K c).map LifetimePath.ofContinuousPath) := by
  intro U hU hUb
  obtain ⟨p, hmeas, hpos, hmass, hcont⟩ := hD U hU hUb
  have hcR : 0 < (c : ℝ) := hc
  refine ⟨fun t => p ((c : ℝ) * t), ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact hmeas _ (mul_pos hcR ht)
  · intro t ht x hx y hy
    exact hpos _ (mul_pos hcR ht) x hx y hy
  · intro t ht x hx B hB
    rw [continuous_lifetime_killedEvent _ U hU t x B hB,
      clockKernel_killedEvent K c hc hU (Real.toNNReal t) x hB]
    have htime : Real.toNNReal ((c : ℝ) * t) = c * Real.toNNReal t := by
      rw [Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe]
    rw [← htime, ← continuous_lifetime_killedEvent
      K U hU ((c : ℝ) * t) x B hB]
    exact hmass _ (mul_pos hcR ht) x hx B hB
  · exact hcont.comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd).continuousOn
      (fun z hz => ⟨mul_pos hcR hz.1, hz.2⟩)

/-- Composing clocks is equality of the actual path kernels. -/
theorem clockKernel_clockKernel {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (K : Kernel E (ContinuousPath E)) (c b : NNReal) :
    clockKernel (clockKernel K c) b = clockKernel K (c * b) := by
  rw [clockKernel, clockKernel, clockKernel, ← Kernel.map_comp_right _
    (ContinuousPath.measurable_rescale _ _) (ContinuousPath.measurable_rescale _ _)]
  congr 1
  funext w
  ext t
  change w (c * (b * t)) = w ((c * b) * t)
  rw [mul_assoc]

@[simp] theorem clockKernel_one {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (K : Kernel E (ContinuousPath E)) : clockKernel K 1 = K := by
  have hid : ContinuousPath.rescale (Homeomorph.refl E) 1 = id := by
    funext w
    exact ContinuousPath.rescale_refl_one w
  rw [clockKernel, hid, Kernel.map_id]

end
end SubdiffusiveProcess.Examples
