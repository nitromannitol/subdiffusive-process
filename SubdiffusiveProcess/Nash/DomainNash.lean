import SubdiffusiveProcess.Nash.Interpolation
import SubdiffusiveProcess.Nash.KernelContraction
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- The real-valued form of the generator-domain Nash estimate. -/
theorem real_nash_of_sobolev {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (d : ℕ) (hd : 2 ≤ d) (f : Lp ℝ 2 mu) (K E F : ℝ) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hF : 0 ≤ F) (hL1 : eLpNorm (f : X → ℝ) 1 mu ≤ ENNReal.ofReal F)
    (hsob : eLpNorm (f : X → ℝ) (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))) mu ^ (2 : ℕ) ≤
      ENNReal.ofReal K * ENNReal.ofReal E) :
    (‖f‖ ^ 2) ^ (1 + 1 / (d : ℝ)) ≤ K * E * F ^ (2 / (d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have h := nash_of_sobolev mu d hd f (Lp.aestronglyMeasurable f)
    (ENNReal.ofReal K) (ENNReal.ofReal E) hsob
  have hpow := ENNReal.rpow_le_rpow hL1 (show 0 ≤ 2 / (d : ℝ) by positivity)
  have hn := h.trans (mul_le_mul_right hpow _)
  have hnR := ENNReal.toReal_mono (by finiteness) hn
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, ← Lp.norm_def, ENNReal.toReal_ofReal hK,
    ENNReal.toReal_ofReal hE, ENNReal.toReal_ofReal hF] at hnR
  convert hnR using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg f)]
  norm_num

end SubdiffusiveProcess.Nash
