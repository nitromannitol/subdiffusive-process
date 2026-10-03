module

public import SubdiffusiveProcess.BesovComparison.ScalarComparison

@[expose] public section

/-! Taking roots without a finite-energy hypothesis, uniformly for p ≥ 1. -/
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.BesovComparison
variable {d : ℕ}

def upperConstant (d : ℕ) : ℝ≥0∞ := 2 * 3 ^ d

theorem one_le_upperConstant (d : ℕ) : 1 ≤ upperConstant d :=
  one_le_mul (by norm_num) (one_le_pow₀ (by norm_num))

theorem one_le_lowerConstant (d : ℕ) : 1 ≤ Gagliardo.gagliardoBesovLowerConstant d := by
  unfold Gagliardo.gagliardoBesovLowerConstant
  exact one_le_mul (by norm_num) (one_le_pow₀ (by norm_num))

theorem overlap_le_upper_mul_gagliardo [NeZero d]
    (s : FractionalOrder) (p : FiniteExponent) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (humeas : Measurable u)
    (hmem : MemLp u p.exponent (normalizedCubeMeasure Q)) :
    exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u hu ≤
      upperConstant d * Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent u := by
  have hp : 0 < p.exponent.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le p.one_le_exponent)) p.lt_top.ne
  have hp1 : 1 ≤ p.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal (by norm_num) p.lt_top.ne).mpr p.one_le_exponent
  apply (ENNReal.rpow_le_rpow_iff hp).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  exact (exactOverlapScalarPSeminorm_rpow_le_gagliardo s p Q u hu humeas hmem).trans
    (mul_le_mul' (ENNReal.le_rpow_self_of_one_le (one_le_upperConstant d) hp1) le_rfl)

theorem gagliardo_le_lower_mul_overlap [NeZero d]
    (s : FractionalOrder) (p : FiniteExponent) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable Q u) (humeas : Measurable u)
    (hmem : MemLp u p.exponent (normalizedCubeMeasure Q)) :
    Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent u ≤
      Gagliardo.gagliardoBesovLowerConstant d *
        exactOverlapFiniteSeminorm (exactOverlapScalarPParameters s p) Q u hu := by
  have hp : 0 < p.exponent.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le p.one_le_exponent)) p.lt_top.ne
  apply (ENNReal.rpow_le_rpow_iff hp).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  exact gagliardo_rpow_le_exactOverlapScalarPSeminorm s p Q u hu humeas hmem

end SubdiffusiveProcess.BesovComparison
