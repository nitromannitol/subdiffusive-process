module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteComponentBudgets
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities

@[expose] public section




open MeasureTheory Homogenization
open Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Cauchy--Schwarz for a symmetric positive semidefinite matrix field, at the
level of the spatial integral. -/
theorem abs_integral_vecDot_matVecMul_le_sqrt_mul_sqrt
    (U : Set (Vec d)) [IsFiniteMeasure (volumeMeasureOn U)]
    (A : Vec d → Mat d) (u v : Vec d → Vec d)
    (hA : ∀ x, (A x).IsSymm)
    (hA0 : ∀ x, ∀ w : Vec d, 0 ≤ vecDot w (matVecMul (A x) w))
    (hu : Integrable (fun x ↦ vecDot (u x) (matVecMul (A x) (u x)))
      (volumeMeasureOn U))
    (hv : Integrable (fun x ↦ vecDot (v x) (matVecMul (A x) (v x)))
      (volumeMeasureOn U))
    (huv : Integrable (fun x ↦ vecDot (u x) (matVecMul (A x) (v x)))
      (volumeMeasureOn U)) :
    |∫ x in U, vecDot (u x) (matVecMul (A x) (v x)) ∂volume| ≤
      Real.sqrt (∫ x in U, vecDot (u x) (matVecMul (A x) (u x)) ∂volume) *
        Real.sqrt (∫ x in U, vecDot (v x) (matVecMul (A x) (v x)) ∂volume) := by
  set mu : Measure (Vec d) := volumeMeasureOn U with hmu
  set X : Vec d → ℝ := fun x ↦ vecDot (u x) (matVecMul (A x) (u x)) with hX
  set Y : Vec d → ℝ := fun x ↦ vecDot (v x) (matVecMul (A x) (v x)) with hY
  set Z : Vec d → ℝ := fun x ↦ vecDot (u x) (matVecMul (A x) (v x)) with hZ
  have hX0 : ∀ x, 0 ≤ X x := fun x ↦ hA0 x (u x)
  have hY0 : ∀ x, 0 ≤ Y x := fun x ↦ hA0 x (v x)
  have hpt : ∀ x, |Z x| ≤ Real.sqrt (X x) * Real.sqrt (Y x) := fun x ↦
    abs_vecDot_matVecMul_le_sqrt_quad_mul_sqrt_quad (hA x) (hA0 x) (u x) (v x)
  have hsqX : Integrable (fun x ↦ Real.sqrt (X x) ^ 2) mu := by
    refine hu.congr ?_
    filter_upwards with x
    rw [Real.sq_sqrt (hX0 x)]
  have hsqY : Integrable (fun x ↦ Real.sqrt (Y x) ^ 2) mu := by
    refine hv.congr ?_
    filter_upwards with x
    rw [Real.sq_sqrt (hY0 x)]
  have hmemX : MemLp (fun x ↦ Real.sqrt (X x)) 2 mu :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        hu.aestronglyMeasurable)).2 hsqX
  have hmemY : MemLp (fun x ↦ Real.sqrt (Y x)) 2 mu :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        hv.aestronglyMeasurable)).2 hsqY
  have hmixInt : Integrable
      (fun x ↦ Real.sqrt (X x) * Real.sqrt (Y x)) mu :=
    hmemX.integrable_mul hmemY
  have hcs : ∫ x, Real.sqrt (X x) * Real.sqrt (Y x) ∂mu ≤
      Real.sqrt (∫ x, Real.sqrt (X x) ^ 2 ∂mu) *
        Real.sqrt (∫ x, Real.sqrt (Y x) ^ 2 ∂mu) :=
    integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      hsqX hsqY
      (Filter.Eventually.of_forall fun x ↦ Real.sqrt_nonneg _)
      (Filter.Eventually.of_forall fun x ↦ Real.sqrt_nonneg _)
  have hXeq : ∫ x, Real.sqrt (X x) ^ 2 ∂mu = ∫ x, X x ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [Real.sq_sqrt (hX0 x)]
  have hYeq : ∫ x, Real.sqrt (Y x) ^ 2 ∂mu = ∫ x, Y x ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [Real.sq_sqrt (hY0 x)]
  calc
    |∫ x, Z x ∂mu| ≤ ∫ x, |Z x| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ x, Real.sqrt (X x) * Real.sqrt (Y x) ∂mu :=
      integral_mono huv.abs hmixInt hpt
    _ ≤ Real.sqrt (∫ x, Real.sqrt (X x) ^ 2 ∂mu) *
          Real.sqrt (∫ x, Real.sqrt (Y x) ^ 2 ∂mu) := hcs
    _ = Real.sqrt (∫ x, X x ∂mu) * Real.sqrt (∫ x, Y x ∂mu) := by
      rw [hXeq, hYeq]

/-- **Cauchy--Schwarz on a cell average.**  Coefficient-agnostic mixed-term
bound in the exact `sqrt * sqrt` shape the finite-majorant assembly
consumes. -/
theorem abs_volumeAverage_vecDot_matVecMul_le_sqrt_mul_sqrt
    (U : Set (Vec d)) [IsFiniteMeasure (volumeMeasureOn U)]
    (A : Vec d → Mat d) (u v : Vec d → Vec d)
    (hA : ∀ x, (A x).IsSymm)
    (hA0 : ∀ x, ∀ w : Vec d, 0 ≤ vecDot w (matVecMul (A x) w))
    (hu : Integrable (fun x ↦ vecDot (u x) (matVecMul (A x) (u x)))
      (volumeMeasureOn U))
    (hv : Integrable (fun x ↦ vecDot (v x) (matVecMul (A x) (v x)))
      (volumeMeasureOn U))
    (huv : Integrable (fun x ↦ vecDot (u x) (matVecMul (A x) (v x)))
      (volumeMeasureOn U)) :
    |volumeAverage U (fun x ↦ vecDot (u x) (matVecMul (A x) (v x)))| ≤
      Real.sqrt (volumeAverage U
          (fun x ↦ vecDot (u x) (matVecMul (A x) (u x)))) *
        Real.sqrt (volumeAverage U
          (fun x ↦ vecDot (v x) (matVecMul (A x) (v x)))) := by
  have hbase := abs_integral_vecDot_matVecMul_le_sqrt_mul_sqrt U A u v
    hA hA0 hu hv huv
  set c : ℝ := ((volume U).toReal)⁻¹ with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [volumeAverage, volumeAverage, volumeAverage, abs_mul,
    abs_of_nonneg hc0, Real.sqrt_mul hc0, Real.sqrt_mul hc0]
  rw [show Real.sqrt c *
        Real.sqrt (∫ x in U, vecDot (u x) (matVecMul (A x) (u x)) ∂volume) *
        (Real.sqrt c *
          Real.sqrt (∫ x in U,
            vecDot (v x) (matVecMul (A x) (v x)) ∂volume)) =
      (Real.sqrt c * Real.sqrt c) *
        (Real.sqrt (∫ x in U,
            vecDot (u x) (matVecMul (A x) (u x)) ∂volume) *
          Real.sqrt (∫ x in U,
            vecDot (v x) (matVecMul (A x) (v x)) ∂volume)) by ring,
    Real.mul_self_sqrt hc0]
  exact mul_le_mul_of_nonneg_left hbase hc0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
