module

public import SubdiffusiveProcess.Examples.ClockResolvent
public import SubdiffusiveProcess.Examples.ClockFiniteDistributions
public import SubdiffusiveProcess.Processes.E7.FellerFromResolvent
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-! # Laplace identification for the actual constant-clock realization -/

open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.Semigroup Set
open MarkovProcess.SubMarkovKernelSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty NNReal

namespace SubdiffusiveProcess.Examples
noncomputable section

/-- The inverse time multiplier, kept positive in the native time carrier. -/
def inverseClock (k : ℝ) (hk : 0 < k) : NNReal := ⟨k⁻¹, (inv_pos.mpr hk).le⟩

theorem inverseClock_pos (k : ℝ) (hk : 0 < k) : 0 < inverseClock k hk := inv_pos.mpr hk

/-- The clocked datum is the Laplace transform of the SAME rescaled realization. -/
theorem clockResolvent_laplace {d : ℕ}
    (P : SubMarkovKernelSemigroup (Fin d → ℝ)) (D : C0ResolventDatum (Fin d → ℝ))
    (hlaplace : ∀ (mu : PositiveShift) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      D.solution mu f x = ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) f x)
    (k : ℝ) (hk : 0 < k) (mu : PositiveShift) (f : C₀(Fin d → ℝ, ℝ))
    (x : Fin d → ℝ) :
    (clockResolvent D k hk).solution mu f x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (clockSemigroup P (inverseClock k hk) (Real.toNNReal t)) f x := by
  let g : ℝ → ℝ := fun t => Real.exp (-(mu : ℝ) * t) *
    kernelIntegral (clockSemigroup P (inverseClock k hk) (Real.toNNReal t)) f x
  have htime (t : ℝ) : inverseClock k hk * Real.toNNReal (k * t) = Real.toNNReal t := by
    rw [Real.toNNReal_mul hk.le]
    have hreal : (k⁻¹ : ℝ) * ((Real.toNNReal k : ℝ) * (Real.toNNReal t : ℝ)) =
        (Real.toNNReal t : ℝ) := by
      rw [Real.coe_toNNReal _ hk.le]
      field_simp
    apply NNReal.coe_injective
    simpa only [inverseClock, NNReal.coe_mul] using! hreal
  have hg (t : ℝ) : g (k * t) = Real.exp (-(clockShift k hk mu : ℝ) * t) *
      kernelIntegral (P (Real.toNNReal t)) f x := by
    dsimp [g, clockSemigroup]
    rw [htime]
    congr 2
    dsimp [clockShift]
    ring
  have h := integral_comp_mul_left_Ioi g 0 hk
  simp only [mul_zero, smul_eq_mul] at h
  simp_rw [hg] at h
  change k * D.solution (clockShift k hk mu) f x = ∫ t in Ioi (0 : ℝ), g t
  rw [hlaplace, h]
  field_simp

end
end SubdiffusiveProcess.Examples
