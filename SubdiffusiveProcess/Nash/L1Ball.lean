module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- L1 balls are closed for convergence in L2, by Fatou's lemma. -/
theorem isClosed_L1Ball {X : Type*} [MeasurableSpace X] (mu : Measure X) (C : ℝ≥0∞) :
    IsClosed {f : Lp ℝ 2 mu | eLpNorm (f : X → ℝ) 1 mu ≤ C} := by
  apply IsSeqClosed.isClosed
  intro f g hf hg
  exact eLpNorm_le_of_tendstoInMeasure (p := 1) (Eventually.of_forall hf)
    (tendstoInMeasure_of_tendsto_Lp hg) (fun n => Lp.aestronglyMeasurable (f n))

/-- The L1 ball viewed in L2 is convex. -/
theorem convex_L1Ball {X : Type*} [MeasurableSpace X] (mu : Measure X) (C : ℝ≥0∞) :
    Convex ℝ {f : Lp ℝ 2 mu | eLpNorm (f : X → ℝ) 1 mu ≤ C} := by
  intro f hf g hg a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hf hg
  change eLpNorm ((a • f + b • g : Lp ℝ 2 mu) : X → ℝ) 1 mu ≤ C
  rw [eLpNorm_congr_ae (Lp.coeFn_add _ _)]
  calc
    _ ≤ eLpNorm ((a • f : Lp ℝ 2 mu) : X → ℝ) 1 mu +
        eLpNorm ((b • g : Lp ℝ 2 mu) : X → ℝ) 1 mu :=
      eLpNorm_add_le le_rfl
    _ = ENNReal.ofReal a * eLpNorm (f : X → ℝ) 1 mu +
        ENNReal.ofReal b * eLpNorm (g : X → ℝ) 1 mu := by
      rw [eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_congr_ae (Lp.coeFn_smul _ _)]
      simp only [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ ENNReal.ofReal a * C + ENNReal.ofReal b * C := by gcongr
    _ = C := by rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab]; simp

end SubdiffusiveProcess.Nash
