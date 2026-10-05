module

public import SubdiffusiveProcess.Analysis.MeasureBallGrowth
public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

/-! Finite sums preserve local measure growth with an explicit cardinality factor.
The result is deterministic and has no stochastic or form assumptions. -/
open MeasureTheory Set SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess

/-- A finite family of unit-cell growth bounds controls its sum at arbitrary centers. -/
theorem finite_sum_measure_unit_cube_growth
    {d : ℕ} {ι : Type*} [Fintype ι] (mu : ι → Measure (SpatialCoordinates d))
    (K t : ℝ) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hg : ∀ i, ∀ x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos,
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      mu i (Metric.ball x rho ∩ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal (K * rho ^ t)) :
    ∀ x : SpatialCoordinates d, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ((∑ i, mu i) (Metric.ball x rho ∩
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))).toReal ≤
        (2 ^ t * (Fintype.card ι : ℝ) * K) * rho ^ t := by
  have hsum : ∀ x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos,
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      (∑ i, mu i) (Metric.ball x rho ∩
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal (((Fintype.card ι : ℝ) * K) * rho ^ t) := by
    intro x hx rho hrho hrho1
    rw [Measure.finsetSum_apply]
    calc
      _ ≤ ∑ i : ι, ENNReal.ofReal (K * rho ^ t) := Finset.sum_le_sum (fun i _ => hg i x hx rho hrho hrho1)
      _ = ENNReal.ofReal (((Fintype.card ι : ℝ) * K) * rho ^ t) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hK (Real.rpow_nonneg hrho.le _))]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  have hall := measure_ball_inter_growth_of_centers_mem (∑ i, mu i)
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) 0
    (Metric.mem_ball_self (by norm_num))
    (Metric.ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1))
    ((Fintype.card ι : ℝ) * K) t (mul_nonneg (Nat.cast_nonneg _) hK) ht hsum
  intro x rho hrho hrho1
  have hbound := hall x rho hrho hrho1
  rw [← mul_assoc] at hbound
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) hK)
      (Real.rpow_nonneg hrho.le _)) hbound

end SubdiffusiveProcess
