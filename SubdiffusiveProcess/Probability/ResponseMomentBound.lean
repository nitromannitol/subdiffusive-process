module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SubdiffusiveProcess.Probability

/-- Two centered error bounds control the full response on a probability space. -/
theorem eLpNorm_le_of_two_centered_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (y y0 : X → ℝ)
    (hy : AEStronglyMeasurable y μ) (hy0 : AEStronglyMeasurable y0 μ)
    (q C δ : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C) (hδ : δ ≤ 1)
    (h1 : eLpNorm (fun x => y0 x - 1) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C * δ))
    (h2 : eLpNorm (fun x => y x - y0 x) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C * δ)) :
    eLpNorm y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (2 * C + 1) := by
  have hqe : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hconst : eLpNorm (fun _ : X => (1 : ℝ)) (ENNReal.ofReal q) μ = 1 := by
    rw [eLpNorm_const' _ hq0 ENNReal.ofReal_ne_top]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
  have hid : y = ((fun x => y x - y0 x) + (fun x => y0 x - 1)) + (fun _ => 1) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have hCD : C * δ ≤ C := mul_le_of_le_one_right hC hδ
  calc
    eLpNorm y (ENNReal.ofReal q) μ ≤
        (eLpNorm (fun x => y x - y0 x) (ENNReal.ofReal q) μ +
          eLpNorm (fun x => y0 x - 1) (ENNReal.ofReal q) μ) + 1 := by
      conv_lhs => rw [hid]
      exact (eLpNorm_add_le (μ := μ) (p := ENNReal.ofReal q)
        hqe).trans (by
          rw [hconst]
          exact add_le_add (eLpNorm_add_le (μ := μ) (p := ENNReal.ofReal q)
            hqe) le_rfl)
    _ ≤ (ENNReal.ofReal C + ENNReal.ofReal C) + 1 :=
      add_le_add (add_le_add (h2.trans (ENNReal.ofReal_le_ofReal hCD))
        (h1.trans (ENNReal.ofReal_le_ofReal hCD))) le_rfl
    _ = ENNReal.ofReal (2 * C + 1) := by
      rw [← ENNReal.ofReal_add hC hC, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (add_nonneg hC hC) (by norm_num)]
      congr 1
      ring

end SubdiffusiveProcess.Probability
