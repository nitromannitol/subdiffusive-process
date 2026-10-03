module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicHighExponent

@[expose] public section

/-!
# Normalized `L^p` restriction to a central descendant

The exact normalized-measure formula in CoarseGraining is converted here to
the real `cubeLpNorm` inequality used in the one-step cell bookkeeping.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Restriction to the central depth-`n` descendant costs the exact
descendant-count factor to the power `1/p`. -/
theorem cubeLpNorm_centralDescendant_le_count_rpow {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) (p : FiniteLpExponent)
    (f : Vec d → ℝ) (hf : MemLp f p.exponent (normalizedCubeMeasure Q)) :
    cubeLpNorm (CubeCalderonZygmund.centralDescendant Q n) p.exponent f ≤
      ((((3 ^ d) ^ n : ℕ) : ℝ) ^ (1 / p.exponent).toReal) *
        cubeLpNorm Q p.exponent f := by
  let N : ℝ := (((3 ^ d) ^ n : ℕ) : ℝ)
  let NE : ℝ≥0∞ := ENNReal.ofReal N
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hnorm :
      eLpNorm f p.exponent
          (normalizedCubeMeasure
            (CubeCalderonZygmund.centralDescendant Q n)) ≤
        NE ^ (1 / p.exponent).toReal *
          eLpNorm f p.exponent (normalizedCubeMeasure Q) := by
    rw [CubeCalderonZygmund.eLpNorm_centralDescendant_eq_rpow_smul_restrict]
    exact mul_le_mul_right
      (eLpNorm_mono_measure f Measure.restrict_le_self) _
  have hrightTop :
      NE ^ (1 / p.exponent).toReal *
        eLpNorm f p.exponent (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      hf.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hrightTop hnorm
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hNpos.le] at hreal
  simpa [cubeLpNorm, N, NE] using hreal

/-- If `2 ≤ p`, the normalized `L²` norm on a central descendant is bounded
by the same count-root factor times the parent normalized `L^p` norm. -/
theorem cubeLpNorm_two_centralDescendant_le_count_rpow {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (f : Vec d → ℝ)
    (hf : MemLp f p.exponent (normalizedCubeMeasure Q)) :
    cubeLpNorm (CubeCalderonZygmund.centralDescendant Q n) 2 f ≤
      ((((3 ^ d) ^ n : ℕ) : ℝ) ^ (1 / p.exponent).toReal) *
        cubeLpNorm Q p.exponent f := by
  let R := CubeCalderonZygmund.centralDescendant Q n
  letI : IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨normalizedCubeMeasure_apply_univ R⟩
  have hfR : MemLp f p.exponent (normalizedCubeMeasure R) :=
    CubeCalderonZygmund.memLp_centralDescendant_of_memLp n hf
  have hdown : eLpNorm f 2 (normalizedCubeMeasure R) ≤
      eLpNorm f p.exponent (normalizedCubeMeasure R) :=
    eLpNorm_le_eLpNorm_of_exponent_le hp
  have htop := hfR.eLpNorm_ne_top
  have hdownReal := ENNReal.toReal_mono htop hdown
  calc
    cubeLpNorm R 2 f ≤ cubeLpNorm R p.exponent f := by
      simpa [cubeLpNorm] using hdownReal
    _ ≤ ((((3 ^ d) ^ n : ℕ) : ℝ) ^ (1 / p.exponent).toReal) *
        cubeLpNorm Q p.exponent f :=
      cubeLpNorm_centralDescendant_le_count_rpow Q n p f hf

/-- Arbitrary finite target-exponent version of the preceding downgrade. -/
theorem cubeLpNorm_centralDescendant_downgrade_le_count_rpow {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) (p : FiniteLpExponent)
    (r : ℝ≥0∞) (hr : r ≤ p.exponent) (f : Vec d → ℝ)
    (hf : MemLp f p.exponent (normalizedCubeMeasure Q)) :
    cubeLpNorm (CubeCalderonZygmund.centralDescendant Q n) r f ≤
      ((((3 ^ d) ^ n : ℕ) : ℝ) ^ (1 / p.exponent).toReal) *
        cubeLpNorm Q p.exponent f := by
  let R := CubeCalderonZygmund.centralDescendant Q n
  letI : IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨normalizedCubeMeasure_apply_univ R⟩
  have hfR : MemLp f p.exponent (normalizedCubeMeasure R) :=
    CubeCalderonZygmund.memLp_centralDescendant_of_memLp n hf
  have hdown : eLpNorm f r (normalizedCubeMeasure R) ≤
      eLpNorm f p.exponent (normalizedCubeMeasure R) :=
    eLpNorm_le_eLpNorm_of_exponent_le hr
  have hdownReal := ENNReal.toReal_mono hfR.eLpNorm_ne_top hdown
  calc
    cubeLpNorm R r f ≤ cubeLpNorm R p.exponent f := by
      simpa [cubeLpNorm] using hdownReal
    _ ≤ ((((3 ^ d) ^ n : ℕ) : ℝ) ^ (1 / p.exponent).toReal) *
        cubeLpNorm Q p.exponent f :=
      cubeLpNorm_centralDescendant_le_count_rpow Q n p f hf

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
